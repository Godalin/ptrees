(* Trusted host boundary: IO, Random.State and a tail-recursive scheduler.
   No control algorithm or sampling algorithm is reimplemented here. *)
module C = Controller
exception Runtime_error of string
let fail s = raise (Runtime_error s)
let limit = 100_000
let nat n =
  if n < 0 || n > limit then fail "integer outside host resource bound";
  let rec go n a = if n = 0 then a else go (n-1) (C.S a) in go n C.O
let integer n =
  let rec go a = function C.O -> a | C.S n ->
    if a >= limit then fail "ticket/value exceeds host resource bound" else go (a+1) n
  in go 0 n
type source = Random of Random.State.t | Replay of int list
type entropy = { source : source; draws : int; trace : out_channel option }
let next bound s =
  let d = integer bound in
  if d <= 0 then fail "invalid ticket bound";
  let value, source = match s.source with
    | Random rng -> Some (Random.State.int rng d), s.source
    | Replay [] -> None, s.source
    | Replay (i::rest) -> Some i, Replay rest
  in
  match value with
  | None -> None, s
  | Some i ->
      if i < 0 || i >= d then fail "ticket outside requested bound";
      (match s.trace with None -> () | Some out -> Printf.fprintf out "%d %d\n%!" d i);
      Some (nat i), {s with source; draws = s.draws + 1}
let remaining s = match s.source with Replay xs -> List.length xs | Random _ -> 0
let reply = function C.Pass -> "pass" | C.Rework -> "rework" | C.Jam -> "jam"
let mode b = if b then "FAST" else "SAFE"
let entry = function
  | C.Accepted j -> Printf.printf "receive %d\n" (integer j)
  | C.Attempted (j,b,r) -> Printf.printf "machine %d %s %s\n" (integer j) (mode b) (reply r)
  | C.Shipped j -> Printf.printf "ship %d\n" (integer j)
  | C.Alarmed j -> Printf.printf "alarm %d\n" (integer j)
  | C.ResetAcknowledged -> print_endline "reset"
let terminal_error = function
  | C.Lost -> fail "Lost: missing probability mass"
  | C.EntropyExhausted -> fail "entropy exhausted (not loss)"
  | C.Timeout -> fail "unexpected timeout in fuel-free execution"
  | C.Returned _ -> fail "unexpected program return"
let rec execute t s = match C.closed_step next t s with
  | C.Continue (u,s') -> execute u s'
  | C.InvalidMeasure _ -> fail "invalid native measure (mass > 1)"
  | C.Done (C.Returned (C.Inl script),s') -> script,s'
  | C.Done (result,_) -> terminal_error result
let prompt text = print_string text; flush stdout; read_line ()
let rec interactive t s = match C.live_step next t s with
  | C.LiveContinue (u,s') -> interactive u s'
  | C.LiveInvalid _ -> fail "invalid native measure (mass > 1)"
  | C.LiveDone (r,_) -> terminal_error r
  | C.NeedOrder (k,s') ->
      let text = prompt "order number (or quit): " in
      if text = "quit" then Printf.printf "experiment stopped; draws=%d\n" s'.draws
      else interactive (k (nat (int_of_string text))) s'
  | C.NeedReply (j,b,k,s') ->
      Printf.printf "machine %d %s\n" (integer j) (mode b);
      let r = match prompt "response (pass/rework/jam): " with
        | "pass" -> C.Pass | "rework" -> C.Rework | "jam" -> C.Jam
        | _ -> fail "unknown machine response"
      in interactive (k r) s'
  | C.DoShip (j,u,s') -> Printf.printf "ship %d\n" (integer j); interactive u s'
  | C.DoAlarm (j,u,s') -> Printf.printf "alarm %d\n" (integer j); interactive u s'
  | C.NeedReset (u,s') ->
      if prompt "reset (ok): " <> "ok" then fail "reset not acknowledged";
      interactive u s'
let main () =
  if Array.length Sys.argv < 4 then fail
    "usage: main.exe (impl|spec) (script|interactive|replay) SEED_OR_TICKETS [--trace NEW_FILE]";
  let implementation = match Sys.argv.(1) with "impl" -> true | "spec" -> false
    | _ -> fail "choose impl or spec" in
  let command = Sys.argv.(2) in
  let source = if command = "replay" then Replay
      (if Sys.argv.(3) = "" then [] else
       List.map int_of_string (String.split_on_char ',' Sys.argv.(3)))
    else Random (Random.State.make [|int_of_string Sys.argv.(3)|]) in
  let trace = if Array.length Sys.argv = 6 && Sys.argv.(4) = "--trace" then
      Some (open_out_gen [Open_wronly;Open_creat;Open_excl;Open_text] 0o600 Sys.argv.(5))
    else if Array.length Sys.argv = 4 then None else fail "invalid arguments" in
  Fun.protect ~finally:(fun () -> Option.iter close_out trace) (fun () ->
    let s = {source; draws=0; trace} in
    if command = "interactive" then interactive (if implementation then C.live_impl else C.live_spec) s
    else if command = "script" || command = "replay" then begin
      let script,s' = execute (if implementation then C.demo_impl else C.demo_spec) s in
      List.iter entry (C.chronological_log script);
      Printf.printf "experiment=script-exhausted\ndraws=%d\nremaining=%d\n" s'.draws (remaining s')
    end else fail "unknown execution mode")
let () = try main () with
  | Runtime_error s -> prerr_endline s; exit 2
  | Failure s | Invalid_argument s | Sys_error s -> prerr_endline s; exit 2
  | End_of_file -> prerr_endline "device input exhausted (not loss)"; exit 2
