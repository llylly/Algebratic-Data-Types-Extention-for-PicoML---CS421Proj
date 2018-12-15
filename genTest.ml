(*
  Test generator from Stdin for our Algebratic Data Type Extension for PicoML
  CS 421 Unit Project
  Linyi Li & Hanyun Xu
*)

open Common
open Values
open Type_inferencer
open Eval_exp

let parse s = Picomlparse.main Picomllex.token (Lexing.from_string s)

let cur_inst = ref ""

let print_strarr wrap arr = 
let rec work wrap arr = match arr with
  (x :: []) ->  if wrap then print_string "\"" else (); print_string x; if wrap then print_string "\"" else (); print_string "]"
  | (x :: xs) -> if wrap then print_string "\"" else (); print_string x; if wrap then print_string "\"" else (); print_string ";\n"; work wrap xs
  | [] -> print_string "]"
in print_string "["; work wrap arr

let rec value_str value = match value with
  UnitVal -> "UnitVal"
  | BoolVal b -> "BoolVal " ^ (if b then "true" else "false")
  | IntVal i -> "IntVal " ^ (string_of_int i)
  | FloatVal f -> "FloatVal " ^ (string_of_float f)
  | StringVal s -> "StringVal \"" ^ s ^ "\""
  | Closure _ -> "Closure (* to be filled *)"
  | RecVarVal _ -> "RecVarVal (* to be filled *)"
  | PairVal (v1, v2) -> "PairVal (" ^ (value_str v1) ^ ", " ^ (value_str v2) ^ ")"
  | CustomVal (cons, vlist) -> "CustomVal (\"" ^ cons ^ "\", [" ^ varr_str vlist ^ "])"
  | ListVal vlist -> "ListVal [" ^ varr_str vlist ^ "]"
  | Exn i -> "Exn " ^ (string_of_int i)
and varr_str varr = match varr with
  [] -> ""
  | (x:: []) -> value_str x
  | (x:: xs) -> (value_str x) ^ "; " ^ (varr_str xs)

let rec loop (instrs: string list) (res: string list) (gamma: type_env) (beta: typeDec_env) (mem: memory) = 
    try
      let lexbuf = Lexing.from_channel stdin
      in (cur_inst := ""; print_string "> "; flush stdout);
         (try
            let dec = Picomlparse.main (fun lb -> cur_inst := !cur_inst ^ ((Lexing.lexeme lb) ^ " ");
                              match Picomllex.token lb with 
                                EOF -> raise Picomllex.EndInput
                                | r -> r)
                        (lexbuf)
            in 
              print_string "======\n";
              print_strarr true (List.rev instrs);
              print_string ", \n";
              print_strarr false (List.rev res);
              print_string "\n======\n";
              match infer_dec gather_dec_ty_substitution gamma beta dec with
              | None          -> (print_string "\ndoes not type check\n"; 
                                  loop ((!cur_inst ^ ";;"):: instrs) ("None" :: res) gamma beta mem)
              | Some (Proof(hyps,judgement)) -> (match judgement with
                  TypeJudgment (beta') -> (
                    print_string (string_of_env string_of_typeDec beta');
                    print_string "\n";
                    loop ((!cur_inst ^ ";;"):: instrs) ("None" :: res) gamma beta' mem
                  )
                  | _ -> (
                    match eval_dec (dec, mem) with 
                      ((None, value), m) ->
                          (
                            print_string "\nresult:\n";
                            print_string "_ = ";
                            print_value value;
                            print_string "\n";
                            loop ((!cur_inst ^ ";;"):: instrs) (("Some (" ^ (value_str value) ^ ")") :: res) gamma beta mem
                          )
                    | ((Some s,value), m) ->
                          (
                            print_string "\nresult:\n";
                            print_string (s^" = ");
                            print_value value;
                            print_string "\n";
                            (
                              match judgement with DecJudgment (_,_,delta) ->
                                loop ((!cur_inst ^ ";;"):: instrs) (("Some (" ^ (value_str value) ^ ")") :: res) (sum_env delta gamma) beta (*(ins_env gamma s (gen gamma ty))*) m
                                | _ -> raise (Failure "This shouldn't be possible")
                            )
                          )
                  )
                )
          with 
            Failure s -> (print_newline();
                          print_endline s;
                          print_newline();
                          loop ((!cur_inst ^ ";;"):: instrs) ("None" :: res) gamma beta mem)
            | Parsing.Parse_error ->
              (print_string "\ndoes not parse\n";
               loop ((!cur_inst ^ ";;"):: instrs) ("None" :: res) gamma beta mem)
          )
    with Picomllex.EndInput -> exit 0

let _ = loop [] [] [] [] []

(* let proj_rubric = let rec dec_test (slist, rlist) (gamma: type_env) (beta: typeDec_env) (mem: memory) = 
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
      print_string ("Final score: [" ^ (string_of_int score) ^ "/" ^ (string_of_int full_score) ^ "]\n") *)

