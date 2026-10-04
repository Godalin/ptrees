(* Unverified frontend/host boundary: parsing, entropy, scheduling and output.
   Expression evaluation, input validation, elaboration, state interpretation,
   bounded execution and native sampling all come from the extracted module. *)
module P = Pgcl
exception Input_error of string
let fail s = raise (Input_error s)
let limit = 100_000
let nat n =
  let rec go n a = if n = 0 then a else go (n - 1) (P.S a) in
  if n < 0 || n > limit then fail "natural input exceeds [0,100000]";
  go n P.O
let int_of_nat n =
  let rec go i = function
    | P.O -> i
    | P.S n -> if i >= limit then fail "ticket space exceeds resource limit" else go (i+1) n
  in go 0 n
let integer s = try int_of_string s with Failure _ -> fail ("invalid integer: " ^ s)
let positive n =
  let rec go n = if n = 1 then P.XH else
    if n mod 2 = 0 then P.XO (go (n/2)) else P.XI (go (n/2)) in
  go n
let z_of_string s =
  let n = integer s in
  if n < -limit || n > limit then fail "integer literal exceeds [-100000,100000]";
  if n = 0 then P.Z0 else if n > 0 then P.Zpos (positive n) else P.Zneg (positive (-n))
(* Decimal output does not truncate extracted arbitrary-precision integers. *)
let decimal_bit s bit =
  let b = Bytes.of_string s in
  let carry = ref bit in
  for i = Bytes.length b - 1 downto 0 do
    let n = 2 * (Char.code (Bytes.get b i) - 48) + !carry in
    Bytes.set b i (Char.chr (48 + n mod 10)); carry := n / 10
  done;
  (if !carry = 0 then "" else string_of_int !carry) ^ Bytes.to_string b
let string_of_z =
  let rec pos = function
    | P.XH -> "1" | P.XO p -> decimal_bit (pos p) 0 | P.XI p -> decimal_bit (pos p) 1 in
  function P.Z0 -> "0" | P.Zpos p -> pos p | P.Zneg p -> "-" ^ pos p

type sexp = Atom of string | List of sexp list
let read_program path =
  let ch = open_in path in
  Fun.protect ~finally:(fun () -> close_in_noerr ch) (fun () ->
    let n = in_channel_length ch in
    if n > 1_000_000 then fail "program file too large";
    let text = really_input_string ch n in
    let rec space i = if i >= n then i else match text.[i] with
      | ' ' | '\n' | '\r' | '\t' -> space (i+1)
      | ';' -> comment (i+1)
      | _ -> i
    and comment i = if i >= n then i else if text.[i] = '\n' then space (i+1) else comment (i+1) in
    let rec parse depth i =
      if depth > 256 then fail "program nesting limit exceeded";
      let i = space i in
      if i >= n then fail "unexpected end of program";
      match text.[i] with
      | '(' -> items (depth+1) (i+1) []
      | ')' -> fail "unexpected closing parenthesis"
      | _ ->
          let j = ref i in
          while !j < n && not (List.mem text.[!j] ['('; ')'; ' '; '\n'; '\r'; '\t'; ';']) do incr j done;
          Atom (String.sub text i (!j-i)), !j
    and items depth i acc =
      let i = space i in
      if i >= n then fail "unclosed parenthesis";
      if text.[i] = ')' then List (List.rev acc), i+1
      else let x,j = parse depth i in items depth j (x::acc)
    in
    let tree,i = parse 0 0 in
    if space i <> n then fail "extra input after program";
    tree)

let variable s =
  if String.length s < 2 || s.[0] <> 'x' then fail ("expected variable xN: " ^ s);
  nat (integer (String.sub s 1 (String.length s-1)))
let rec arithmetic = function
  | Atom s when String.length s > 0 && s.[0] = 'x' -> P.Read (variable s)
  | Atom s -> P.Number (z_of_string s)
  | List [Atom "+"; a; b] -> P.Plus (arithmetic a, arithmetic b)
  | List [Atom "-"; a; b] -> P.Minus (arithmetic a, arithmetic b)
  | List [Atom "*"; a; b] -> P.Times (arithmetic a, arithmetic b)
  | _ -> fail "invalid arithmetic expression"
let rec condition = function
  | Atom "true" -> P.Boolean true | Atom "false" -> P.Boolean false
  | List [Atom "="; a; b] -> P.Equal (arithmetic a, arithmetic b)
  | List [Atom "<"; a; b] -> P.Less (arithmetic a, arithmetic b)
  | List [Atom "<="; a; b] -> P.LessEqual (arithmetic a, arithmetic b)
  | List [Atom "not"; b] -> P.Not (condition b)
  | List [Atom "and"; a; b] -> P.And (condition a, condition b)
  | List [Atom "or"; a; b] -> P.Or (condition a, condition b)
  | _ -> fail "invalid Boolean expression"
let rec command = function
  | Atom "skip" -> P.Skip | Atom "diverge" -> P.Diverge
  | List [Atom "set"; Atom x; e] -> P.Assign (variable x, arithmetic e)
  | List (Atom "seq" :: cs) ->
      List.fold_right (fun c rest -> P.Sequence (command c, rest)) cs P.Skip
  | List [Atom "if"; b; yes; no] -> P.If (condition b, command yes, command no)
  | List [Atom "choice"; Atom n; Atom d; a; b] ->
      let d = integer d in
      (* Binary rational coins use at most d*d materialized tickets. Check
         before calling the extracted compiler, not after allocation. *)
      if d > 256 then fail "probability denominator exceeds resource limit 256";
      P.Choice (nat (integer n), nat d, command a, command b)
  | List [Atom "while"; b; body] -> P.While (condition b, command body)
  | _ -> fail "invalid command"

type entropy = Generated of Random.State.t | Replay of in_channel
let next trace bound entropy =
  let b = int_of_nat bound in
  if b = 0 then fail "zero entropy bound";
  let ticket = match entropy with
    | Generated rng -> Some (Random.State.int rng b)
    | Replay ch ->
        (match input_line ch with
         | line -> (match String.split_on_char ' ' (String.trim line) with
             | [bound; value] ->
                 if integer bound <> b then fail "replay bound mismatch";
                 Some (integer value)
             | _ -> fail "malformed replay: expected BOUND TICKET")
         | exception End_of_file -> None)
  in
  match ticket with
  | None -> None, entropy
  | Some i ->
      if i < 0 || i >= b then fail "replay ticket outside bound";
      (match trace with None -> () | Some ch -> Printf.fprintf ch "%d %d\n%!" b i);
      Some (nat i), entropy

let unbounded next tree seed =
  let rec loop t s = match P.machine_step next t s with
    | P.Continue (t,s) -> loop t s | P.Done (r,s) -> r,s
  in loop tree seed

let usage = "usage: main.exe FILE [--fuel N | --unbounded] [--seed N | --replay FILE] [--trials N] [--init xN=Z,...] [--observe xN,...] [--trace NEW_FILE]"
let main () =
  if Array.length Sys.argv = 2 && Sys.argv.(1) = "--help" then (print_endline usage; exit 0);
  if Array.length Sys.argv < 2 then fail usage;
  let fuel = ref (Some 10000) and seed = ref None and replay = ref None in
  let trials = ref 1 and entries = ref [] and observe = ref ["x0"] and trace = ref None in
  let rec options i = if i < Array.length Sys.argv then
    if Sys.argv.(i) = "--unbounded" then (fuel := None; options (i+1)) else begin
      if i+1 >= Array.length Sys.argv then fail "option needs a value";
      let v = Sys.argv.(i+1) in
      (match Sys.argv.(i) with
       | "--fuel" -> let n = integer v in ignore (nat n); fuel := Some n
       | "--seed" -> seed := Some (integer v)
       | "--replay" -> replay := Some v
       | "--trace" -> trace := Some v
       | "--trials" -> let n = integer v in if n < 1 || n > limit then fail "invalid trial count"; trials := n
       | "--observe" -> observe := String.split_on_char ',' v
       | "--init" -> entries := List.map (fun e -> match String.split_on_char '=' e with
           | [x;z] -> variable x, z_of_string z | _ -> fail "initial store expects xN=Z") (String.split_on_char ',' v)
       | opt -> fail ("unknown option: " ^ opt));
      options (i+2)
    end
  in options 2;
  if !seed <> None && !replay <> None then fail "choose seed or replay, not both";
  let vars = List.map (fun s -> s, variable s) !observe in
  let program = match P.compile (command (read_program Sys.argv.(1))) with
    | Some c -> c | None -> fail "invalid probability: require 0 <= numerator <= denominator and denominator > 0" in
  let initial = P.initial_store !entries in
  let entropy = match !replay with Some file -> Replay (open_in file)
    | None -> Generated (match !seed with Some n -> Random.State.make [|n|] | None -> Random.State.make_self_init ()) in
  Fun.protect ~finally:(fun () -> match entropy with Replay ch -> close_in_noerr ch | _ -> ()) (fun () ->
    let trace = Option.map (fun path -> open_out_gen [Open_wronly; Open_creat; Open_excl; Open_text] 0o600 path) !trace in
    Fun.protect ~finally:(fun () -> Option.iter close_out_noerr trace) (fun () ->
      let counts = Hashtbl.create 16 in
      let rec simulate n entropy =
        if n = 0 then () else
        let result, entropy = match !fuel with
          | Some n -> P.bounded (next trace) (nat n) program initial entropy
          | None -> unbounded (next trace) (P.start program initial) entropy in
        let label = match result with
          | P.Returned s -> "Returned " ^ String.concat "," (List.map (fun (name,x) -> name ^ "=" ^ string_of_z (s x)) vars)
          | P.Lost -> "Lost" | P.Timeout -> "Timeout" | P.EntropyExhausted -> "EntropyExhausted" in
        Hashtbl.replace counts label (1 + Option.value ~default:0 (Hashtbl.find_opt counts label));
        simulate (n-1) entropy
      in simulate !trials entropy;
      Printf.printf "trials=%d\n" !trials;
      Hashtbl.fold (fun label n xs -> (label,n)::xs) counts [] |> List.sort compare |>
        List.iter (fun (label,n) -> Printf.printf "%s count=%d frequency=%.6f\n" label n (float n /. float !trials));
      print_endline "Frequencies use all trials, including timeouts/source failures. Host PRNG is not verified."))

let () =
  Sys.catch_break true;
  try main () with
  | Sys.Break -> prerr_endline "Interrupted (not a program result)"; exit 130
  | Input_error s | Sys_error s | Failure s | Invalid_argument s -> prerr_endline ("Error: " ^ s); exit 2
  | Stack_overflow | Out_of_memory -> prerr_endline "Resource failure (not Lost or divergence)"; exit 2
