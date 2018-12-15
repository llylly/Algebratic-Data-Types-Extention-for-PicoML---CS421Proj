(*
 * This file will be preprocessed to generate the actual OCaml file.
 *)

(*
  Project tests for our Algebratic Data Type Extension for PicoML
  CS 421 Unit Project
  Linyi Li & Hanyun Xu
*)

// #define TEST0ARG(WEIGHT, FNAME)\
//     #FNAME, mptest WEIGHT (ss_pair0 Solution.FNAME Eval_exp.FNAME)
// #define TEST1ARG(WEIGHT, FNAME, ARG1)\
//     #FNAME^" "^#ARG1, mptest WEIGHT (ss_pair1 Solution.FNAME Eval_exp.FNAME ARG1)
// #define TEST2ARG(WEIGHT, FNAME, ARG1, ARG2)\
//     #FNAME^" "^#ARG1^" "^#ARG2, mptest WEIGHT (ss_pair2 Solution.FNAME Eval_exp.FNAME ARG1 ARG2)
// #define TEST3ARG(WEIGHT, FNAME, ARG1, ARG2, ARG3)\
//     #FNAME^" "^#ARG1^" "^#ARG2^" "^#ARG3, mptest WEIGHT (ss_pair3 Solution.FNAME Eval_exp.FNAME ARG1 ARG2 ARG3)
// #define TEST4ARG(WEIGHT, FNAME, ARG1, ARG2, ARG3, ARG4)\
//     #FNAME^" "^#ARG1^" "^#ARG2^" "^#ARG3^" "^#ARG4, mptest WEIGHT (ss_pair4 Solution.FNAME Eval_exp.FNAME ARG1 ARG2 ARG3 ARG4)
// #define TEST5ARG(WEIGHT, FNAME, ARG1, ARG2, ARG3, ARG4, ARG5)\
//     #FNAME^" "^#ARG1^" "^#ARG2^" "^#ARG3^" "^#ARG4^" "^#ARG5, mptest WEIGHT (ss_pair5 Solution.FNAME Eval_exp.FNAME ARG1 ARG2 ARG3 ARG4 ARG5)

// #define TEST1ARG_TWOFUN(WEIGHT, FNAME1, FNAME2, ARG1)\
//     #FNAME1^" "^#ARG1, mptest WEIGHT (ss_pair1 FNAME1 FNAME2 ARG1)
// #define TEST2ARG_TWOFUN(WEIGHT, FNAME1, FNAME2, ARG1, ARG2)\
//     #FNAME1^" "^#ARG1^" "^#ARG2, mptest WEIGHT (ss_pair2 FNAME1 FNAME2 ARG1 ARG2)
// #define TEST3ARG_TWOFUN(WEIGHT, FNAME1, FNAME2, ARG1, ARG2, ARG3)\
//     #FNAME1^" "^#ARG1^" "^#ARG2^" "^#ARG3, mptest WEIGHT (ss_pair3 FNAME1 FNAME2 ARG1 ARG2 ARG3)

open Grader
open Test
open Common
open Values
open Type_inferencer
open Eval_exp

let parse s = Picomlparse.main Picomllex.token (Lexing.from_string s)

(*
 * use a timeout of 4 seconds
 *)

// let mptest weight pair = compare (=) 4 weight pair

// #include "tests"

#include "proj_tests"

let proj_rubric = let rec dec_test (slist, rlist) (gamma: type_env) (beta: typeDec_env) (mem: memory) = 
    match (slist, rlist) with
      (s:: ss, r:: rs) -> (try 
        let dec = parse s in (
          match infer_dec gather_dec_ty_substitution gamma beta dec with
            None -> (
              print_string "\ndoes not type check\n"; 
              (match r with None -> dec_test (ss, rs) gamma beta mem | Some _ -> false))
            | Some (Proof(hyps,judgement)) -> (match judgement with
                TypeJudgment (betap) -> (
                  (* print_string (string_of_env string_of_typeDec betap); *)
                  (* print_string "\n"; *)
                  dec_test (ss, rs) gamma betap mem
                )
                | _ -> (match eval_dec (dec, mem) with 
                  ((None, value), m) -> (match r with
                    Some r -> if value = r then dec_test (ss, rs) gamma beta m else false
                    | None -> false
                    )
                  | ((Some s,value), m) -> (match judgement with
                    DecJudgment (_, _, delta) -> (match r with
                      Some r -> if value = r then dec_test (ss, rs) (sum_env delta gamma) beta m else false
                      | None -> false)
                    | _ -> raise (Failure "This shouldn't be possible"))
                )
              )
          )
        with 
          Failure s -> (match r with Some _ -> false | None -> dec_test (ss, rs) gamma beta mem)
          | Parsing.Parse_error -> (match r with Some _ -> false | None -> dec_test (ss, rs) gamma beta mem)
        )
      | ([], []) -> true
      | _ -> raise (Failure "Illegal test case.")
  in
    let test_each (w, s, r) = (let rec print_case s r = (match (s, r) with
          (si:: ss, ri:: rs) -> print_string (si ^ "\n  Result: "); (match ri with Some ri -> print_value ri | None -> print_string "Illegal exp"); print_newline (); print_case ss rs
          | ([], []) -> ()
          | _ -> raise (Failure "Illegal test case.")
        ) in 
      let pass = dec_test (s, r) [] [] [] in
        print_string ("[" ^ (string_of_int (if pass then w else 0)) ^ "/" ^ (string_of_int w) ^ "]\n");
        print_case s r; 
        print_newline ();
        if pass then w else 0
      )
    in
    let score = 
      List.fold_left (+) 0 (List.map (fun x -> test_each x) eval_dec_test_cases)
    and full_score =
      List.fold_left (+) 0 (List.map (fun (w, s, r) -> w) eval_dec_test_cases) 
    in
      print_string ("Final score: [" ^ (string_of_int score) ^ "/" ^ (string_of_int full_score) ^ "]\n")


// let _ = Main.main rubric extra_rubric rubric_title rubric_version

let _ = proj_rubric