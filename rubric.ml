(*
 * This file will be preprocessed to generate the actual OCaml file.
 *)

(*
  Project tests for our Algebratic Data Type Extension for PicoML
  CS 421 Unit Project
  Linyi Li & Hanyun Xu
*)
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






(*
  Project tests for our Algebratic Data Type Extension for PicoML
  CS 421 Unit Project
  Linyi Li & Hanyun Xu
*)

let eval_dec_test_cases = [
  1, [
    "type node = EN | N of int * tree and tree = EM | M of node * tree;;"
    ;"EN;;"
    ;"(N (1, (M (EN, EM))));;"
  ], [
    None
    ;Some (CustomVal ("EN", []))
    ;Some (CustomVal ("N", [IntVal 1; CustomVal ("M", [CustomVal ("EN", []); CustomVal ("EM", [])])]))
  ];

  1, [
    "type int_tup = NULLINT | ONEINT of int | TWOINT of int * int | TRIINT of int * int * int;;"
    ;"let a = ONEINT (5);;"
    ;"let b = TRIINT (10, 5, 7);;"
    ;"let c = TWOINT (30, 40);;"
    ;"~TRIINT (b);;"
    ;"~TRIINT (a);;"
    ;"~TRIINT (c);;"
    ;"~TWOINT (c);;"
  ], [
    None
    ;Some (CustomVal ("ONEINT", [IntVal 5]))
    ;Some (CustomVal ("TRIINT", [IntVal 10; IntVal 5; IntVal 7]))
    ;Some (CustomVal ("TWOINT", [IntVal 30; IntVal 40]))
    ;Some (PairVal (IntVal 10, PairVal (IntVal 5, IntVal 7)))
    ;None
    ;None
    ;Some (PairVal (IntVal 30, IntVal 40))
  ];

  1, [" type dlist = ONE of ( int list ) | TWO of ( ( int list ) * ( int list ) ) ;;";
  " let a = ONE ( [ 1 ; 2 ; 3 ] ) ;;";
  " let b = TWO ( ( [ 1 ; 2 ; 3 ] , [ 3 ; 2 ; 1 ] ) ) ;;";
  " ~ONE ( a ) ;;";
  " ( hd ( fst ( ~TWO ( b ) ) ) ) = ( hd ( tl ( tl ( snd ( ~TWO ( b ) ) ) ) ) ) ;;"],
  [None;
  Some (CustomVal ("ONE", [ListVal [IntVal 1; IntVal 2; IntVal 3]]));
  Some (CustomVal ("TWO", [PairVal (ListVal [IntVal 1; IntVal 2; IntVal 3], ListVal [IntVal 3; IntVal 2; IntVal 1])]));
  Some (ListVal [IntVal 1; IntVal 2; IntVal 3]);
  Some (BoolVal true)]
]

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




let _ = proj_rubric
