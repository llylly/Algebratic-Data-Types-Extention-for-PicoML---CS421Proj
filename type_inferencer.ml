
open Common

(*-----------------------------------------------*)

(*constraint list*)
type consList = (monoTy * monoTy) list


(*applying a substitution to a proof*)
let rec proof_lift_subst f = function
    Proof(assum, ExpJudgment(gamma, exp, monoTy)) ->
    Proof(List.map (proof_lift_subst f) assum,
          ExpJudgment(env_lift_subst f gamma, exp, monoTy_lift_subst f monoTy))
 | Proof(assum, DecJudgment(gamma, dec, delta)) ->
    Proof(List.map (proof_lift_subst f) assum,
          DecJudgment(env_lift_subst f gamma, dec, env_lift_subst f delta))
 | Proof(assum, TypeJudgment(delta)) ->
    Proof(assum, TypeJudgment(delta))

let rec proof_rename_tyvars f = function
    Proof(assum, ExpJudgment(gamma, exp, monoTy)) ->
    Proof(List.map (proof_rename_tyvars f) assum,
          ExpJudgment(env_rename_tyvars f gamma, exp,
                      monoTy_rename_tyvars f monoTy))
 | Proof(assum, DecJudgment(gamma, dec, delta)) ->
    Proof(List.map (proof_rename_tyvars f) assum,
          DecJudgment(env_rename_tyvars f gamma, dec,
                      env_rename_tyvars f delta))
 | Proof(assum, TypeJudgment(delta)) ->
    Proof(assum, TypeJudgment(delta))

let get_ty = function
   None       -> raise(Failure "None")
 | Some(ty,p) -> ty

let get_proof = function
   None       -> raise(Failure "None")
 | Some(ty,p) -> p

let infer_exp gather_exp (gamma:type_env) (beta: typeDec_env) (exp:exp) = 
  let ty = fresh() in
  let result = 
    match gather_exp gamma beta exp ty with
       None         -> None
     | Some(proof,sigma) -> match ty with
          | TyVar n -> Some (subst_fun sigma n, proof_lift_subst sigma proof)
          | _       -> None
  in let _ = reset() in
  result;;

let infer_dec gather_dec (gamma:type_env) (beta:typeDec_env) (dec:dec) =
  let result = 
    match gather_dec gamma beta dec with
       None -> None
     | Some(proof,sigma) -> Some (proof_lift_subst sigma proof)
  in let _ = reset() in
  result;;

let string_of_constraints c =
  let rec aux c =
     match c with 
     | [] -> ""
     | [(s,t)] ->  (string_of_monoTy s^ " --> "^ string_of_monoTy t)
     | (s,t)::c' -> (string_of_monoTy s^ " --> "^ string_of_monoTy t^
		     "; "^ aux c')
  in ("["^ aux c^ "]\n")

 
let string_of_substitution s =
  let rec aux s =
     match s with 
     | [] -> ""
     | [(i,t)] -> ((string_of_typeVar i)  ^ " |--> " ^ string_of_monoTy t)
     | (i,t)::s' -> (((string_of_typeVar i)  ^ " |--> ")^
                     string_of_monoTy t^ "; "^ aux s')
  in ("["^ aux s^ "]\n")


let niceInfer_exp gather_exp (gamma:type_env) (beta: typeDec_env) exp = 
  let ty = fresh()
  in
  let result = 
    match gather_exp gamma beta exp ty with
     None ->
      (print_string("Failure: No type for expression: "^
       string_of_exp exp^ "\n"^
       "in the environment: "^
       string_of_env string_of_polyTy gamma^ "\n");
       raise (Failure ""))
   | Some (p,s) ->
   (string_of_proof p^
	(*
   "Constraints: "^
   string_of_constraints c ^
   "Unifying..."^
   match unify c with
     None -> ("Failure: No solution for these constraints!\n"^
              raise (Failure ""))
   | Some s ->
	*)
   ("Unifying substitution: "^
    string_of_substitution s^
    "Substituting...\n"^
    let new_p = proof_lift_subst s p in
    string_of_proof new_p)) in
  let _ = reset() in
  result;;

let niceInfer_dec
    (gather_dec:(type_env -> typeDec_env -> dec -> (proof * type_env * substitution) option))
    (beta:typeDec_env)
    (gamma:type_env) dec = 
  let result = 
    match gather_dec gamma beta dec with
     None ->
      (print_string("Failure: No type for declaraion: "^
       string_of_dec dec^ "\n"^
       "in the environment: "^
       string_of_env string_of_polyTy gamma^ "\n");
       raise (Failure ""))
   | Some (p,d,s) ->
   (string_of_proof p^
   ("Unifying substitution: "^
    string_of_substitution s^
    "Substituting...\n"^
    let new_p = proof_lift_subst s p in
    string_of_proof new_p)) in
  let _ = reset() in
  result;;

(* Collect all the TyVar indices in a proof *)

let rec collectTypeVars ty lst =
  match ty with
    TyVar m -> m::lst
  | TyConst(st, typelst) -> List.fold_left (fun xl x -> collectTypeVars x xl) lst typelst

let rec collectFreeTypeVars bty ty lst =
  match ty with
    TyVar m -> if List.mem m bty then lst else m::lst
  | TyConst(st, typelst) ->
    List.fold_left (fun xl x -> collectFreeTypeVars bty x xl) lst typelst

let collectPolyTyVars (bty,mty) lst = collectFreeTypeVars bty mty lst

let collectEnvVars (gamma:type_env) lst =
    List.fold_left (fun tys (_,pty)-> collectPolyTyVars pty tys) lst gamma

let collectJdgVars jdg lst =
    match jdg with ExpJudgment(gamma, exp, monoTy) ->
        collectEnvVars gamma (collectTypeVars monoTy lst)
    | DecJudgment(gamma, dec, delta) ->
        collectEnvVars gamma (collectEnvVars delta lst)
    | TypeJudgment(delta) -> 
      []

let rec collectProofVars prf lst =
  match prf with Proof (assum, jdg)
   -> collectAssumVars assum (collectJdgVars jdg lst)
and collectAssumVars assum lst =
  match assum with 
    []     -> lst
  | p::ps -> collectAssumVars ps (collectProofVars p lst)

let canonicalize_proof prf_opt =
    match prf_opt with None -> None
    | Some(ty, prf) ->
  let (varlst,_) =
    List.fold_right (fun x (xl,idx) -> ((x,idx)::xl), idx+1) 
      (delete_duplicates (collectProofVars prf (collectTypeVars ty []))) 
      ([],1)
  in Some(monoTy_rename_tyvars varlst ty, proof_rename_tyvars varlst prf)

let canon = canonicalize_proof

let canon_dec prf_opt =
    match prf_opt with None -> None
    | Some prf ->
  let (varlst,_) =
    List.fold_right (fun x (xl,idx) -> ((x, idx)::xl), idx+1) 
      (delete_duplicates (collectProofVars prf []))
      ([],1)
  in Some(proof_rename_tyvars varlst prf)

(* ML3's inferencer *)

let rec lookup_cons beta cons = match beta with
  (tname, (_, conslst)):: betas -> (match (List.filter (fun c -> (fst c) = cons) conslst) with
    (consname, comps):: _ -> Some (tname, comps)
    | [] -> lookup_cons betas cons
  )
  | [] -> None

let rec gather_exp_ty_substitution (gamma: type_env) (beta: typeDec_env) (exp: exp) (tau: monoTy) =
    let judgment = ExpJudgment(gamma, exp, tau) in
(*
    let _ = print_string ("Trying to type "^ string_of_judgment judgment^"\n") in
*)
    let result =
    match exp with 
    ConstructExp (cons, explst) -> (match (lookup_cons beta cons) with
      Some (tname, comps) -> (let rec work explst comps proof subst = (match (explst, comps) with
          (exp:: es, comp:: cs) -> (match (gather_exp_ty_substitution (env_lift_subst subst gamma) beta exp comp) with
              Some (pf, sigma) -> work es cs (pf::proof) (subst_compose sigma subst)
              | None -> None
            )
          | ([], []) -> Some (proof, subst)
          | _ -> None
        ) in (match (work explst comps [] []) with
          Some (pflist, sigma) -> (match unify [(tau, monoTy_lift_subst sigma (make_userType tname))]
            with None -> None
            | Some sigma' -> Some(Proof(pflist, judgment), subst_compose sigma' sigma))
          | None -> None 
        ))
      | None -> None
      )
    | TestExp (cons, exp) -> (match (lookup_cons beta cons) with
      Some (tname, _) -> (match (gather_exp_ty_substitution gamma beta exp (make_userType tname)) with
        Some (pf, sigma) -> (match unify [(tau, monoTy_lift_subst sigma bool_ty)] with
          None -> None
          | Some sigma' -> Some(Proof([pf], judgment), subst_compose sigma' sigma))
        | None -> None)
      | None -> None
      )
    | DestructExp (cons, exp) -> (match (lookup_cons beta cons) with
      Some (tname, comps) -> (match (gather_exp_ty_substitution gamma beta exp (make_userType tname)) with
        Some (pf, sigma) -> let rec make_comp_type comps = (match comps with
            (c :: []) -> c
            | (c :: cs) -> mk_pair_ty c (make_comp_type cs)
            | [] -> unit_ty
          ) in (match unify [(tau, monoTy_lift_subst sigma (make_comp_type comps))]
            with None -> None
            | Some sigma' -> Some(Proof([pf], judgment), subst_compose sigma' sigma)
          )
        | None -> None)
      | None -> None
      )
    | ConstExp c ->
         let tau' = const_signature c in
         (match unify [(tau, freshInstance tau')]
          with None       -> None
             | Some sigma -> Some(Proof([],judgment), sigma))
    | VarExp x -> (match lookup_env gamma x with 
        None -> None
        | Some gamma_x -> (
            match unify [(tau, freshInstance gamma_x)]
              with None       -> None
              | Some sigma -> Some(Proof([],judgment), sigma)
          )
      )
    | BinOpAppExp (binop, e1,e2) ->
      let tau' = binop_signature binop in
      let tau1 = fresh() in
      let tau2 = fresh() in
      (match gather_exp_ty_substitution gamma beta e1 tau1
       with None -> None
       | Some(pf1, sigma1) ->
         (match gather_exp_ty_substitution (env_lift_subst sigma1 gamma) beta e2 tau2
          with None -> None
          | Some (pf2, sigma2) ->
            let sigma21 = subst_compose sigma2 sigma1 in
            (match unify[(monoTy_lift_subst sigma21
                          (mk_fun_ty tau1 (mk_fun_ty tau2 tau)),
                         freshInstance tau')]
             with None -> None
             | Some sigma3 -> 
               Some(Proof([pf1;pf2], judgment),subst_compose sigma3 sigma21))))
    | MonOpAppExp (monop, e1) ->
      let tau' = monop_signature monop in
      let tau1 = fresh() in
      (match gather_exp_ty_substitution gamma beta e1 tau1
       with None -> None
       | Some(pf, sigma) ->
         (match unify[(monoTy_lift_subst sigma (mk_fun_ty tau1 tau),
                       freshInstance tau')]
          with None -> None
          | Some subst ->
            Some(Proof([pf], judgment),
                 subst_compose subst sigma)))
    | IfExp(e1,e2,e3) ->
      (match gather_exp_ty_substitution gamma beta e1 bool_ty
       with None -> None
       | Some(pf1, sigma1) ->
         (match gather_exp_ty_substitution
                (env_lift_subst sigma1 gamma) beta e2 (monoTy_lift_subst sigma1 tau)
          with None -> None
          | Some (pf2, sigma2) ->
            let sigma21 = subst_compose sigma2 sigma1 in
            (match gather_exp_ty_substitution
                   (env_lift_subst sigma21 gamma) beta e3
                   (monoTy_lift_subst sigma21 tau)
             with  None -> None
             | Some(pf3, sigma3) ->
               Some(Proof([pf1;pf2;pf3], judgment), subst_compose sigma3 sigma21))))
    | FunExp(x,e) ->
      let tau1 = fresh() in
      let tau2 = fresh() in
      (match gather_exp_ty_substitution
             (ins_env gamma x (polyTy_of_monoTy tau1)) beta e tau2
       with None -> None
       | Some (pf, sigma) ->
         (match unify [(monoTy_lift_subst sigma tau,
                        monoTy_lift_subst sigma (mk_fun_ty tau1 tau2))]
          with None -> None
          | Some sigma1 ->
            Some(Proof([pf],judgment), subst_compose sigma1 sigma)))
    | AppExp(e1,e2) ->
      let tau1 = fresh() in
      (match gather_exp_ty_substitution gamma beta e1 (mk_fun_ty tau1 tau)
       with None -> None
       | Some(pf1, sigma1) ->
         (match gather_exp_ty_substitution (env_lift_subst sigma1 gamma) beta e2
                                           (monoTy_lift_subst sigma1 tau1)
          with None -> None
          | Some (pf2, sigma2) ->
            Some(Proof([pf1;pf2], judgment), subst_compose sigma2 sigma1)))
    | RaiseExp e ->
      (match gather_exp_ty_substitution gamma beta e int_ty
       with None -> None
       | Some(pf, sigma) -> Some(Proof([pf],judgment), sigma))
    | LetInExp(x,e1,e2)  -> 
       let tau1 = fresh() in
       (match gather_exp_ty_substitution gamma beta e1 tau1
	with None -> None
	   | Some(pf1, sigma1) -> 
	      let delta_env = make_env x (gen (env_lift_subst sigma1 gamma) 
					      (monoTy_lift_subst sigma1 tau1)) in
	      (match gather_exp_ty_substitution 
		       (sum_env delta_env (env_lift_subst sigma1 gamma)) beta e2
                         (monoTy_lift_subst sigma1 tau)
	       with None -> None
		  | Some (pf2,sigma2) ->
		     let sigma21 = subst_compose sigma2 sigma1 in
		     Some(Proof([pf1;pf2], judgment), sigma21)))
    | LetRecInExp(f,x,e1,e2) ->
       let tau1  = fresh() in
       let tau2 = fresh() in
       let tau1_to_tau2 = mk_fun_ty tau1 tau2 in
       (match gather_exp_ty_substitution
		(ins_env (ins_env gamma f (polyTy_of_monoTy tau1_to_tau2))
			  x (polyTy_of_monoTy tau1)) beta
		e1 tau2
	with None -> None
	   | Some(pf1, sigma1) -> 
              let sigma1_gamma = env_lift_subst sigma1 gamma in
	      let sigma1_tau1_to_tau2 = monoTy_lift_subst sigma1 tau1_to_tau2 in
	      (match gather_exp_ty_substitution
                     (ins_env sigma1_gamma f (gen sigma1_gamma sigma1_tau1_to_tau2))
		     beta e2 (monoTy_lift_subst sigma1 tau)
	       with None -> None
		  | Some(pf2,sigma2) ->
		     let sigma21 = subst_compose sigma2 sigma1 in
		     Some(Proof([pf1;pf2], judgment),sigma21)))
    | TryWithExp (e,intopt1,e1, match_list) ->
      (match (gather_exp_ty_substitution gamma beta e tau)
       with None -> None
       | Some (pf, sigma) ->
         (match
           List.fold_left
           (fun part_result -> fun (intopti, ei) ->
            (match part_result with None -> None
             | Some (rev_pflist, comp_sigmas) ->
               (match gather_exp_ty_substitution
                      (env_lift_subst comp_sigmas gamma) beta ei
                      (monoTy_lift_subst comp_sigmas tau)
                with None -> None
                | Some (pfi, sigmai) ->
                  Some (pfi :: rev_pflist, subst_compose sigmai comp_sigmas))))
           (Some([pf], sigma))
           ((intopt1,e1):: match_list)
           with None -> None
           | Some (rev_pflist, comp_subst) ->
             Some(Proof(List.rev rev_pflist, judgment), comp_subst)))

in (
(*
    (match result
     with None ->
      print_string ("Failed to type "^string_of_judgment judgment^"\n")
     | Some (_, subst) -> print_string ("Succeeded in typing "^
                               string_of_judgment judgment^"\n"^
"  with substitution "^ string_of_substitution subst ^"\n"));
*)
    result)

let rec gather_comp_types (comps: monoTy list) = match comps with
  (c:: cs) -> (match c with
      TyVar i -> []
      | TyConst (cons, clst) -> cons:: (gather_comp_types clst)
    ) @ gather_comp_types cs
  | [] -> []

let rec gather_dec_ty_substitution (gamma: type_env) (beta: typeDec_env) dec =
    match dec with 
      | Anon e ->
          let tau = fresh() in
            (match gather_exp_ty_substitution gamma beta e tau
	            with None -> None
	            | Some(pf, sigma) -> Some(Proof([pf],DecJudgment (gamma, dec, [])), sigma))
      | Let(x,e) -> 
          let tau = fresh() in
            (match gather_exp_ty_substitution gamma beta e tau
	            with None -> None
	            | Some(pf, sigma) -> 
	              let delta_env = make_env x (gen (env_lift_subst sigma gamma) (monoTy_lift_subst sigma tau)) in
                  Some(Proof([pf],DecJudgment (gamma, dec, delta_env)), sigma))
      | LetRec(f,x,e) ->
          let tau1 = fresh() in
          let tau2 = fresh() in
          let tau1_to_tau2 = mk_fun_ty tau1 tau2 in
            (match gather_exp_ty_substitution
		          (ins_env (ins_env gamma f (polyTy_of_monoTy tau1_to_tau2)) x (polyTy_of_monoTy tau1)) beta e tau2
	          with None -> None
	            | Some(pf, sigma) -> 
                let sigma_gamma = env_lift_subst sigma gamma in
	              let sigma_tau1_to_tau2 = monoTy_lift_subst sigma tau1_to_tau2 in
                let delta_env = (ins_env sigma_gamma f (gen sigma_gamma sigma_tau1_to_tau2)) in 
	                Some(Proof([pf],DecJudgment (gamma, dec, delta_env)), sigma))
      | TypeStat(tplst) -> (
          let beta' = List.filter (fun x -> let tp = fst x in List.length (List.filter (fun y -> fst y = tp) tplst) == 0) beta in
            let existing_tps = List.map (fst) beta' in
              let all_tps = existing_tps @ (List.map (fst) tplst) @ internal_ty in
                let existing_conss = List.flatten (List.map (fun x -> List.map (fst) (snd (snd x))) beta') in
                  let all_conss = existing_conss @ (List.flatten (List.map (fun x -> List.map (fst) (snd x)) tplst)) in
                    let rec work (tplst: typeDec list) = (match tplst with
                      ((tp_name, conss): typeDec):: tplsts -> (
                        let cond1 = (List.length (List.filter (fun x -> x = tp_name) all_tps) = 1) and
                          cond2 = (List.length (List.filter (not) (List.map (fun cons -> (List.length (List.filter (fun x -> x = (fst cons)) all_conss)) = 1) conss)) = 0) and
                          cond3 = (List.length (List.filter (not) (List.flatten (List.map (fun cons -> List.map (fun tp -> List.length (List.filter (fun x -> x = tp) all_tps) = 1) (gather_comp_types (snd cons))) conss))) = 0)
                        in
                          if (not cond1) then (print_string "Duplicate type name both in existing defs and this statement."; false)
                          else (if (not cond2) then (print_string "Duplicate construct name both in existing construct names and this statement."; false)
                          else (if (not cond3) then (print_string "Every component in every constructs should be find in existing type defs or this statement."; false)
                          else work tplsts))
                        )
                      | [] -> true
                    ) in
                      match work tplst with
                        true -> Some(Proof([], TypeJudgment ((List.map (fun x -> (fst x, x)) tplst) @ beta')), [])
                        | false -> None
          )


