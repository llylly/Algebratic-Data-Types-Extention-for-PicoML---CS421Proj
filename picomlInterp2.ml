(*
  interactive-parser.ml - DO NOT EDIT
*)

open Common
open Type_inferencer
open Values
open Picomlparse
open Solution

open Printf
open Printexc

(* Try to detect if something is getting piped in *)
let is_interactive = 0 = (Sys.command "[ -t 0 ]")

let _ =
  (if is_interactive
      then print_endline "\nWelcome to the Student parser \n"
      else ());
  let rec loop (gamma: type_env) (beta: typeDec_env) (mem: memory) = 
    try
      let lexbuf = Lexing.from_channel stdin
      in (if is_interactive 
            then (print_string "> "; flush stdout)
            else ());
         (try
            let dec = main (fun lb -> 
                              match Picomllex.token lb with 
                                EOF -> raise Picomllex.EndInput
                                | r -> r)
                        lexbuf 
            in match infer_dec gather_dec_ty_substitution gamma beta dec with
              | None          -> (print_string "\ndoes not type check\n";
                                  loop gamma beta mem)
              | Some (Proof(hyps,judgement)) -> (match judgement with
                  TypeJudgment (beta') -> (
                    print_string (string_of_env string_of_typeDec beta');
                    print_string "\n";
                    loop gamma beta' mem
                  )
                  | _ -> (
                    match eval_dec (dec, mem) with 
                      ((None, value), m) ->
                          (
                            print_string "\nresult:\n";
                            print_string "_ = ";
                            print_value value;
                            print_string "\n";
                            loop gamma beta mem
                          )
                    | ((Some s,value), m) ->
                          (
                            print_string "\nresult:\n";
                            print_string (s^" = ");
                            print_value value;
                            print_string "\n";
                            (
                              match judgement with DecJudgment (_,_,delta) ->
                                loop (sum_env delta gamma) beta (*(ins_env gamma s (gen gamma ty))*) m
                                | _ -> raise (Failure "This shouldn't be possible")
                            )
                          )
                  )
                )
          with 
            Failure s -> (print_newline();
                          print_endline s;
                          print_newline();
                          loop gamma beta mem)
            | Parsing.Parse_error ->
              (print_string "\ndoes not parse\n";
               loop gamma beta mem)
          )
    with Picomllex.EndInput -> exit 0
  in (loop [] [] [])
