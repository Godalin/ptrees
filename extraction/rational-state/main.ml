(* Only CLI and bounded entropy provisioning are handwritten. All rational
   arithmetic, state handling, recursive control flow and outcome decisions
   are extracted. PRNG quality is not a Rocq theorem. *)
let limit = 100_000

let nat n =
  let rec loop n acc = if n = 0 then acc else loop (n - 1) (Rational.S acc) in
  loop n Rational.O

let int_of_nat n =
  let rec loop acc = function
    | Rational.O -> acc
    | Rational.S n ->
        if acc >= limit then invalid_arg "extracted natural exceeds host resource limit";
        loop (acc + 1) n
  in loop 0 n

let bounded_number name text =
  let n = int_of_string text in
  if n < 0 || n > limit then invalid_arg (name ^ " must be in [0,100000]");
  n

type source = Replay of int list | Generated of Random.State.t * int
type entropy = { source : source; drawn_rev : int list }

let next bound entropy =
  let bound = int_of_nat bound in
  if bound = 0 then invalid_arg "unexpected zero ticket bound";
  let supplied = match entropy.source with
    | Replay [] | Generated (_, 0) -> None
    | Replay (i :: rest) -> Some (i, Replay rest)
    | Generated (rng, count) ->
        (* Do not mutate the input entropy state: repeated calls on the same
           seed state are deterministic, as in the runner's pure contract. *)
        let rng' = Random.State.copy rng in
        let i = Random.State.int rng' bound in
        Some (i, Generated (rng', count - 1))
  in
  match supplied with
  | None -> None, entropy
  | Some (i, source) ->
      Some (nat i), { source; drawn_rev = i :: entropy.drawn_rev }

let parse_trace text =
  if String.length text > 1_000_000 then invalid_arg "replay too long";
  if text = "" then [] else
    let xs = List.map (bounded_number "ticket") (String.split_on_char ',' text) in
    if List.length xs > limit then invalid_arg "too many replay tickets";
    xs

let main () =
  let fuel, initial, source = match Array.to_list Sys.argv with
    | [_; "replay"; fuel; initial; trace] ->
        bounded_number "fuel" fuel, bounded_number "initial" initial,
        Replay (parse_trace trace)
    | [_; "seed"; fuel; initial; seed; count] ->
        bounded_number "fuel" fuel, bounded_number "initial" initial,
        Generated (Random.State.make [|int_of_string seed|], bounded_number "entropy length" count)
    | [_; "random"; fuel; initial; count] ->
        bounded_number "fuel" fuel, bounded_number "initial" initial,
        Generated (Random.State.make_self_init (), bounded_number "entropy length" count)
    | _ -> invalid_arg "usage: main.exe replay FUEL INITIAL TICKETS | seed FUEL INITIAL SEED COUNT | random FUEL INITIAL COUNT"
  in
  let outcome, rest = Rational.rational_counter next (nat fuel) (nat initial)
      {source; drawn_rev = []} in
  let result = match outcome with
    | Rational.Returned n -> "Returned " ^ string_of_int (int_of_nat n)
    | Rational.Lost -> "Lost"
    | Rational.Timeout -> "Timeout"
    | Rational.EntropyExhausted -> "EntropyExhausted"
  in
  let remaining = match rest.source with Replay xs -> List.length xs | Generated (_, n) -> n in
  let trace = String.concat "," (List.map string_of_int (List.rev rest.drawn_rev)) in
  Printf.printf "%s\nremaining=%d\nconsumed=%s\n" result remaining trace

let () = try main () with
  | Invalid_argument message | Failure message -> prerr_endline message; exit 2
