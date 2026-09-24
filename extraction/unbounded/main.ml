(* Trusted host glue: tail-recursive scheduling, CLI, PRNG and optional
   streaming traces. The tree, step and rational ticket sampler are extracted.
   There is NO transition fuel or draw budget. A divergent sample stays busy. *)
module S = Simulation

exception Runtime_error of string
let fail message = raise (Runtime_error message)

(* This guards finite ticket representation, NOT the number of execution
   steps. The extracted compiler still materializes its ticket table. *)
let ticket_limit = 100_000
let int_of_nat n =
  let rec loop acc = function
    | S.O -> acc
    | S.S n ->
        if acc >= ticket_limit then fail "ticket bound exceeds host resource limit";
        loop (acc + 1) n
  in loop 0 n
let nat n =
  let rec loop n acc = if n = 0 then acc else loop (n - 1) (S.S acc) in
  loop n S.O
let ticket text =
  let n = int_of_string text in
  if n < 0 || n > ticket_limit then invalid_arg "ticket must be in [0,100000]";
  n
let increment n =
  if n = max_int then fail "host counter overflow" else n + 1

type source = Replay of int list | Replay_file of in_channel | Generated of Random.State.t
type entropy = { source : source; draws : int; trace : out_channel option }

let next bound state =
  let bound = int_of_nat bound in
  if bound = 0 then fail "unexpected zero ticket bound";
  let supplied = match state.source with
    | Replay [] -> None
    | Replay (i :: rest) -> Some (i, Replay rest)
    | Replay_file channel ->
        (match input_line channel with
         | line ->
             (match String.split_on_char ' ' (String.trim line) with
              | [b; i] ->
                  if int_of_string b <> bound then fail "replay bound mismatch";
                  Some (ticket i, state.source)
              | _ -> fail "malformed trace: expected BOUND TICKET")
         | exception End_of_file -> None)
    | Generated rng ->
        (* Host effects are intentionally outside the proved pure runner. *)
        Some (Random.State.int rng bound, state.source)
  in
  match supplied with
  | None -> None, state
  | Some (i, source) ->
      if i < 0 || i >= bound then fail "ticket outside requested bound";
      (match state.trace with
       | None -> ()
       | Some out -> Printf.fprintf out "%d %d\n%!" bound i);
      Some (nat i), {state with source; draws = increment state.draws}

(* No recursive forcing of a complete tree and no repeated restart with
   larger fuel. Each call resumes exactly the residual extracted tree. *)
let execute tree entropy =
  let rec loop steps tree entropy =
    match S.machine_step next tree entropy with
    | S.Continue (tree, entropy) -> loop (increment steps) tree entropy
    | S.Done (outcome, entropy) -> outcome, entropy, increment steps
    | S.InvalidMeasure _ -> fail "native measure has mass greater than one"
  in loop 0 tree entropy

let result_name = function
  | S.Returned true -> "Returned true"
  | S.Returned false -> "Returned false"
  | S.Lost -> "Lost"
  | S.EntropyExhausted -> fail "entropy exhausted (not missing probability mass)"
  | S.Timeout -> fail "unexpected Timeout from the fuel-free step"

let parse_trace text =
  if String.length text > 1_000_000 then invalid_arg "inline replay too long; use replay-file";
  if text = "" then [] else List.map ticket (String.split_on_char ',' text)

let positive text =
  let n = int_of_string text in
  if n <= 0 then invalid_arg "trial count must be positive";
  n

let usage =
  "usage: main.exe (vn|direct|lost|partial|spin|ret|overweight) \
   (sample SEED | random | replay TICKETS | replay-file PATH | \
    stats TRIALS SEED | stats-random TRIALS) [--trace NEW_PATH]"

let with_trace path f =
  match path with
  | None -> f None
  | Some path ->
      (* Never overwrite a replay or existing user file. *)
      let channel = open_out_gen [Open_wronly; Open_creat; Open_excl; Open_text] 0o600 path in
      Fun.protect ~finally:(fun () -> close_out_noerr channel) (fun () -> f (Some channel))

let main () =
  let args, trace_path = match List.rev (List.tl (Array.to_list Sys.argv)) with
    | path :: "--trace" :: rest -> List.rev rest, Some path
    | _ -> List.tl (Array.to_list Sys.argv), None
  in
  let program, tree, args = match args with
    | name :: rest ->
        let tree = match name with
          | "vn" -> S.von_neumann_third
          | "direct" -> S.direct_fair
          | "lost" -> S.lost
          | "partial" -> S.partial
          | "spin" -> S.spin
          | "ret" -> S.returned
          | "overweight" -> S.overweight
          | _ -> invalid_arg usage
        in name, tree, rest
    | _ -> invalid_arg usage
  in
  let trials, source = match args with
    | ["sample"; seed] -> None, Generated (Random.State.make [|int_of_string seed|])
    | ["random"] -> None, Generated (Random.State.make_self_init ())
    | ["replay"; text] -> None, Replay (parse_trace text)
    | ["replay-file"; path] -> None, Replay_file (open_in path)
    | ["stats"; n; seed] -> Some (positive n), Generated (Random.State.make [|int_of_string seed|])
    | ["stats-random"; n] -> Some (positive n), Generated (Random.State.make_self_init ())
    | _ -> invalid_arg usage
  in
  Fun.protect
    ~finally:(fun () -> match source with Replay_file c -> close_in_noerr c | _ -> ())
    (fun () -> with_trace trace_path (fun trace ->
      let state = {source; draws = 0; trace} in
      match trials with
      | None ->
          let result, rest, steps = execute tree state in
          Printf.printf "%s\nsteps=%d\ndraws=%d\n" (result_name result) steps rest.draws;
          (match rest.source with Replay xs -> Printf.printf "remaining=%d\n" (List.length xs) | _ -> ())
      | Some trials ->
          let rec simulate remaining state yes no lost =
            if remaining = 0 then state, yes, no, lost else
            let result, state, _ = execute tree state in
            match result with
            | S.Returned true -> simulate (remaining - 1) state (yes + 1) no lost
            | S.Returned false -> simulate (remaining - 1) state yes (no + 1) lost
            | S.Lost -> simulate (remaining - 1) state yes no (lost + 1)
            | _ -> ignore (result_name result); assert false
          in
          let rest, yes, no, lost = simulate trials state 0 0 0 in
          Printf.printf "program=%s\ntrials=%d\ntrue=%d\nfalse=%d\nlost=%d\ndraws=%d\n"
            program trials yes no lost rest.draws;
          (* Frequencies divide by ALL trials, not just successful returns. *)
          Printf.printf "true_frequency=%.6f\nfalse_frequency=%.6f\nlost_frequency=%.6f\n"
            (float yes /. float trials) (float no /. float trials) (float lost /. float trials);
          if program = "vn" || program = "direct" then
            print_endline "theory: true=1/2 false=1/2 lost=0 (ideal randomness; not a PRNG proof)"))

let () =
  Sys.catch_break true;
  try main () with
  | Sys.Break -> prerr_endline "Interrupted (not a program result)"; exit 130
  | Runtime_error message | Invalid_argument message | Failure message | Sys_error message ->
      prerr_endline ("Execution error: " ^ message); exit 2
  | Stack_overflow | Out_of_memory ->
      prerr_endline "Execution resource failure (not missing probability mass)"; exit 2
