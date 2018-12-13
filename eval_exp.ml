open Common;;

let const_to_val c = (match c with
	BoolConst b -> BoolVal b
	| IntConst i -> IntVal i
	| FloatConst f -> FloatVal f
	| StringConst s -> StringVal s
	| NilConst -> ListVal []
	| UnitConst -> UnitVal
)

let monOpApply op v = (match op with
		HdOp -> (match v with
			ListVal (x:: xs) -> x
			| ListVal [] -> Exn 0
			| _ -> raise (Failure "Unknown operand.")
			)
		| TlOp -> (match v with
			ListVal (x:: xs) -> ListVal xs
			| ListVal [] -> Exn 0
			| _ -> raise (Failure "Unknown operand.")
			)
		| PrintOp -> (match v with
			StringVal s -> print_string s; UnitVal
			| _ -> raise (Failure "Unknown operand.")
			)
		| IntNegOp -> (match v with
			IntVal i -> IntVal (-i)
			| _ -> raise (Failure "Unknown operand.")
			)
		| FstOp -> (match v with
			PairVal (fst, snd) -> fst
			| _ -> raise (Failure "Unknown operand.")
			)
		| SndOp -> (match v with
			PairVal (fst, snd) -> snd
			| _ -> raise (Failure "Unknown operand.")
			)
	)

let binOpApply binop (v1,v2) = (match binop with
		IntPlusOp -> (match (v1, v2) with
			(IntVal i1, IntVal i2) -> IntVal (i1 + i2)
			| _ -> raise (Failure "Operands type not match")
			)
		| IntMinusOp -> (match (v1, v2) with
			(IntVal i1, IntVal i2) -> IntVal (i1 - i2)
			| _ -> raise (Failure "Operands type not match")
			)
		| IntTimesOp -> (match (v1, v2) with
			(IntVal i1, IntVal i2) -> IntVal (i1 * i2)
			| _ -> raise (Failure "Operands type not match")
			)
		| IntDivOp -> (match (v1, v2) with
			(IntVal i1, IntVal i2) -> if i2 = 0 then Exn 0 else IntVal (i1 / i2)
			| _ -> raise (Failure "Operands type not match")
			)
		| FloatPlusOp -> (match (v1, v2) with
			(FloatVal f1, FloatVal f2) -> FloatVal (f1 +. f2)
			| _ -> raise (Failure "Operands type not match")
			)
		| FloatMinusOp -> (match (v1, v2) with
			(FloatVal f1, FloatVal f2) -> FloatVal (f1 -. f2)
			| _ -> raise (Failure "Operands type not match")
			)
		| FloatTimesOp -> (match (v1, v2) with
			(FloatVal f1, FloatVal f2) -> FloatVal (f1 *. f2)
			| _ -> raise (Failure "Operands type not match")
			)
		| FloatDivOp -> (match (v1, v2) with
			(FloatVal f1, FloatVal f2) -> if f2 = 0.0 then Exn 0 else FloatVal (f1 /. f2)
			| _ -> raise (Failure "Operands type not match")
			)
		| ConcatOp -> (match (v1, v2) with
			(StringVal s1, StringVal s2) -> StringVal (s1 ^ s2)
			| _ -> raise (Failure "Operands type not match")
			)
		| ConsOp -> (match (v1, v2) with
			(_, ListVal l) -> ListVal (v1 :: l)
			| _ -> raise (Failure "Operands type not match")
			)
		| CommaOp -> PairVal (v1, v2)
		| EqOp -> if v1 = v2 then BoolVal true else BoolVal false
		| GreaterOp -> if v1 > v2 then BoolVal true else BoolVal false
		| ModOp -> (match (v1, v2) with
			(IntVal i1, IntVal i2) -> IntVal (i1 mod i2)
			| _ -> raise (Failure "Operands type not match")
			)
		| ExpoOp -> (match (v1, v2) with
			(FloatVal f1, FloatVal f2) -> FloatVal (f1 ** f2)
			| _ -> raise (Failure "Operands type not match")
			)
	)

let rec eval_exp (exp, m) = (match exp with
	ConstExp c -> const_to_val c
	| VarExp x -> (match lookup_env m x with
		Some v -> (match v with
			RecVarVal (g, y, e, m') -> Closure (y, e, ins_env m' g (RecVarVal (g, y, e, m')))
			| _ -> v
			)
		| None -> raise (Failure "Should be in memory")
		)
	| MonOpAppExp (mon, e) -> (let v = eval_exp (e, m) in
			(match v with
				Exn i -> Exn i
				| _ -> monOpApply mon v
			)
		)
	| BinOpAppExp (bin, e1, e2) -> (let v1 = eval_exp (e1, m) and v2 = eval_exp (e2, m) in 
			(match (v1, v2) with
				(Exn i, _) -> Exn i
				| (_, Exn j) -> Exn j
				| _ -> binOpApply bin (v1, v2)
			)
		)
	| IfExp (e1, e2, e3) -> (match eval_exp (e1, m) with
		BoolVal true -> eval_exp (e2, m)
		| BoolVal false -> eval_exp (e3, m)
		| Exn i -> Exn i
		| _ -> raise (Failure "Type not match")
		)
	| LetInExp (x, e1, e2) -> (let v1 = eval_exp (e1, m) in
			(match v1 with
				Exn i -> Exn i
				| _ -> eval_exp (e2, ins_env m x v1)
			)
		)
	| LetRecInExp (f, x, e1, e2) -> eval_exp (e2, (ins_env m f (RecVarVal (f, x, e1, m))))
	| FunExp (x, e1) -> Closure (x, e1, m)
	| AppExp (e1, e2) -> (match eval_exp (e1, m) with
			Closure (x, e', m') -> let v' = eval_exp (e2, m) in
				eval_exp (e', ins_env m' x v')
			| Exn i -> Exn i
			| _ -> raise (Failure "Operands type not match")
		)
	| RaiseExp e -> (match eval_exp (e, m) with
			IntVal i -> Exn i
			| Exn i -> Exn i
			| _ -> raise (Failure "Operands type not match")
		)
	| TryWithExp (e, i, e1, l) -> (let v = eval_exp (e, m) in
			(match v with
				Exn j -> (let rec work no l =
						(match l with
							[] -> None
							| (None, e) :: ls -> Some (eval_exp (e, m))
							| (Some i, e) :: ls -> if i = no then Some (eval_exp (e, m)) else work no ls
						)
					in match (work j ((i, e1) :: l)) with
						Some v' -> v'
						| None -> Exn j
					)
				| _ -> v
			)
		)
)

let eval_dec (dec, m) = (match dec with
	Anon exp -> (let value = eval_exp (exp, m) in ((None, value), m))
	| Let (x, exp) -> (let value = eval_exp (exp, m) in ((Some x, value), ins_env m x value))
	| LetRec (f, x, exp) -> ((Some f, RecVarVal (f, x, exp, m)), ins_env m f (RecVarVal (f, x, exp, m)))
	)

	
