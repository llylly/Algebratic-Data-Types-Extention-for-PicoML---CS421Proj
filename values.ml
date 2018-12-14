
open Common

(*********************************************)
(*                  values                   *)

type memory = (string * value) list
and value =
    UnitVal                                       | BoolVal of bool
  | IntVal of int                                 | FloatVal of float
  | StringVal of string                           | PairVal of value * value
  | Closure of string * exp * memory              | ListVal of value list
  | RecVarVal of string * string * exp * memory   | Exn of int
  | CustomVal of string * (value list)

let make_mem x y = ([(x,y)]:memory)
let rec lookup_mem (gamma:memory) x =
  match gamma with
     []        -> raise (Failure ("identifier "^x^" unbound"))
   | (y,z)::ys -> if x = y then z else lookup_mem ys x
let sum_mem (delta:memory) (gamma:memory) = ((delta@gamma):memory)
let ins_mem (gamma:memory) x y = sum_mem (make_mem x y) gamma

(*value output*)
let rec print_value v =
   match v with
    CustomVal (cons, vlist) -> 
        let rec print_vlist vlist = match vlist with
            (v:: []) -> print_value v
            | (v:: vs) -> (print_value v; print_string ", "; print_vlist vs)
            | [] -> ()
        in (print_string cons; print_string " ("; print_vlist vlist; print_string ")")
  | UnitVal           -> print_string "()"
  | IntVal n          -> if n < 0 then (print_string "~"; print_int (abs n)) else print_int n 
  | FloatVal r        -> print_float r
  | BoolVal true      -> print_string "true"
  | BoolVal false     -> print_string "false"
  | StringVal s       -> print_string ("\"" ^  (String.escaped s) ^ "\"")
  | PairVal (v1,v2)   -> print_string "(";
                         print_value v1; print_string ", ";
                         print_value v2;
                         print_string ")";
  | ListVal l         -> print_string "[";
                         (let rec pl = function
                              []     -> print_string "]"
                            | v::vl  -> print_value v;
                                        if vl <> []
                                        then
                                           print_string "; ";
                                        pl vl
                              in pl l)
  | Closure (x, e, m) -> print_string ("<some closure>")
  | RecVarVal (f, x, e, m)  -> print_string ("<some recvar>")
  | Exn n -> (print_string "(Exn "; print_int n; print_string ")")

let compact_memory m =
  let rec comp m rev_comp_m =
      (match m with [] -> List.rev rev_comp_m
        | (x,y) :: m' ->
           if List.exists (fun (x',_) -> x = x') rev_comp_m
              then comp m' rev_comp_m
           else comp m' ((x,y)::rev_comp_m))
  in comp m []

(*memory output*)
let print_memory m =
    let cm = compact_memory m in
    let rec print_m m = 
    (match m with
        []           -> ()
      | (x, v) :: m' -> print_m m';
                        print_string ("val "^x ^ " = ");
                        print_value v;
                        print_string (";\n") ) in
    print_m cm
