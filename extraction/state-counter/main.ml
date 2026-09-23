(* Only command-line parsing and entropy provisioning are handwritten.
   The recursive tree, native rational sampler, state handler and fuelled
   runner are all extracted from Rocq. Random.State is a PRNG, not a proved
   mathematical uniform oracle. Replay is the reproducible interface. *)
let nat n =
  let rec loop n acc = if n = 0 then acc else loop (n - 1) (Counter.S acc) in
  loop n Counter.O

let int_of_nat n =
  let rec loop acc = function Counter.O -> acc | Counter.S n -> loop (acc + 1) n in
  loop 0 n

let bounded_number name text =
  let n = int_of_string text in
  if n < 0 || n > 100_000 then invalid_arg (name ^ " must be in [0,100000]");
  n

let bits_of_string text =
  List.init (String.length text) (fun i ->
    match text.[i] with
    | '0' -> false | '1' -> true
    | _ -> invalid_arg "replay must contain only 0 and 1")

let string_of_bits bits =
  String.of_seq (List.to_seq (List.map (fun b -> if b then '1' else '0') bits))

let main () =
  let fuel, initial, bits =
    match Array.to_list Sys.argv with
    | [_; "replay"; fuel; initial; trace] ->
        if String.length trace > 100_000 then invalid_arg "replay too long";
        bounded_number "fuel" fuel, bounded_number "initial" initial, bits_of_string trace
    | [_; "seed"; fuel; initial; seed; count] ->
        let state = Random.State.make [|int_of_string seed|] in
        let count = bounded_number "entropy length" count in
        bounded_number "fuel" fuel, bounded_number "initial" initial,
        List.init count (fun _ -> Random.State.bool state)
    | _ -> invalid_arg "usage: main.exe replay FUEL INITIAL BITS | seed FUEL INITIAL SEED COUNT"
  in
  let outcome, remaining = Counter.counter_replay (nat fuel) (nat initial) bits in
  let result = match outcome with
    | Counter.Returned n -> "Returned " ^ string_of_int (int_of_nat n)
    | Counter.Lost -> "Lost"
    | Counter.Timeout -> "Timeout"
    | Counter.EntropyExhausted -> "EntropyExhausted"
  in
  Printf.printf "%s\nremaining=%d\nreplay=%s\n" result (int_of_nat remaining) (string_of_bits bits)

let () = try main () with
  | Invalid_argument message | Failure message -> prerr_endline message; exit 2
