(* ========================================================================= *)
(* OPENTHEORY PROOF LOGGING FOR HOL LIGHT                                    *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

module Export =
struct

(* ------------------------------------------------------------------------- *)
(* Imperative logging dictionaries.                                          *)
(* ------------------------------------------------------------------------- *)

type log_dict = Log_dict of bool * int ref * int Object_map.t ref;;

let new_log_dict defs =
    let next_key = 0 in
    let object_map = Object_map.empty in
    Log_dict (defs, ref next_key, ref object_map);;

let defs_log_dict (Log_dict (defs,_,_)) = defs;;

let next_key_log_dict (Log_dict (_,next_key,_)) =
    let k = !next_key in
    let () = next_key := k + 1 in
    k;;

let peek_log_dict (Log_dict (_,_,object_map)) obj =
    if not (Object_map.mem obj (!object_map)) then None
    else Some (Object_map.find obj (!object_map));;

let save_log_dict (Log_dict (_,_,object_map)) (k,obj) =
    let () = object_map := Object_map.add obj k (!object_map) in
    ();;

(* ------------------------------------------------------------------------- *)
(* Setting up the log files: part 1                                          *)
(* ------------------------------------------------------------------------- *)

type log_state =
     Not_logging
   | Ready_logging
   | Active_logging of out_channel * log_dict;;

let log_env () =
    try (let r = Sys.getenv "OPENTHEORY_LOGGING" in
         if r = "0" then 0 else 2)
    with Not_found -> 1;;

let log_state =
    let initial_log_state =
        let l = log_env () in
        if l < 2 then Not_logging else
        let () = report "Logging the OpenTheory standard library" in
        Ready_logging in
    ref initial_log_state;;

let log_raw s =
    match (!log_state) with
      Active_logging (h,_) -> output_string h (s ^ "\n")
    | _ -> ();;

(* ------------------------------------------------------------------------- *)
(* Logging primitive types                                                   *)
(* ------------------------------------------------------------------------- *)

let log_num n = log_raw (string_of_int n);;

let log_name s = log_raw (Name.to_string s);;

let log_type_var_name s = log_name (Name.mk_type_var s);;

let log_type_op_name s =
    let n = Name.mk_type_op s in
    let n =
        match export_type_op_from_the_interpretation n with
          [] -> n
        | [n] -> n
        | _ :: _ :: _ -> failwith ("ambiguous export for type operator " ^ s) in
    log_name n;;

let log_const_name s =
    let n = Name.mk_const s in
    let n =
        match export_const_from_the_interpretation n with
          [] -> n
        | [n] -> n
        | _ :: _ :: _ -> failwith ("ambiguous export for constant " ^ s) in
    log_name n;;

let log_var_name s = log_name (Name.mk_var s);;

let log_command s = log_raw s;;

let log_nil () = log_command "nil";;

let log_list (log : 'a -> unit) =
    let rec logl l =
        match l with
          [] ->
          let () = log_nil () in
          ()
        | h :: t ->
          let () = log h in
          let () = logl t in
          let () = log_command "cons" in
          () in
    logl;;

let log_unit () = log_nil ();;

let log_sing (log_a : 'a -> unit) a =
    let () = log_a a in
    let () = log_nil () in
    let () = log_command "cons" in
    ();;

let log_pair (log_a : 'a -> unit) (log_b : 'b -> unit) (a,b) =
    let () = log_a a in
    let () = log_sing log_b b in
    let () = log_command "cons" in
    ();;

let log_type_var s = log_type_var_name s;;

(* ------------------------------------------------------------------------- *)
(* Logging terms and theorems.                                               *)
(* ------------------------------------------------------------------------- *)

let (log_term,log_thm,log_clear) =
    let peek_type_op_def t =
        match !log_state with
          Active_logging (_,ld) ->
          if defs_log_dict ld then peek_type_op_definition t else None
        | _ -> failwith "Export.peek_const_def: not actively logging" in
    let peek_const_def c =
        match !log_state with
          Active_logging (_,ld) ->
          if defs_log_dict ld then peek_const_definition c else None
        | _ -> failwith "Export.peek_const_def: not actively logging" in
    let next_key () =
        match !log_state with
          Active_logging (_,ld) -> next_key_log_dict ld
        | _ -> failwith "Export.next_key: not actively logging" in
    let peek obj =
        match !log_state with
          Active_logging (_,ld) -> peek_log_dict ld obj
        | _ -> failwith "Export.peek: not actively logging" in
    let save_top_obj obj =
        match !log_state with
          Active_logging (_,ld) ->
          (match peek obj with
             Some k -> k
           | None ->
             let k = next_key () in
             let () = save_log_dict ld (k,obj) in
             let () = log_num k in
             let () = log_command "def" in
             k)
        | _ -> failwith "Export.save_top_obj: not actively logging" in
    let save_top () =
        let () =
            match !log_state with
              Active_logging _ -> ()
            | _ -> failwith "Export.save_top: not actively logging" in
         let k = next_key () in
         let () = log_num k in
         let () = log_command "def" in
         k in
    let log_clear () =
        let rec clear_up_to k =
            if k = 0 then () else
            let k = k - 1 in
            let () = log_num k in
            let () = log_command "remove" in
            let () = log_command "pop" in
            clear_up_to k in
        let () = clear_up_to (next_key ()) in
        () in
    let get_saved k =
        let () = log_num k in
        let () = log_command "ref" in
        () in
    let saved obj =
        match (peek obj) with
          Some k ->
            let () = get_saved k in
            true
        | None ->
            false in
    let rec log_type_op_def (exists_th,(ar,ra)) =
        let range ty = hd (tl (snd (dest_type ty))) in
        let (predTm,repAbsREqRTm) = dest_comb (concl ra) in
        let (iffTm,predTm) = dest_comb predTm in
        let rTm = rand predTm in
        let (absRepATm,aTm) = dest_comb (concl ar) in
        let (eqTm,absRepATm) = dest_comb absRepATm in
        let (absTm,repTm) = dest_comb absRepATm in
        let (repTm,_) = dest_const (rator repTm) in
        let (absTm,newTy) = dest_const absTm in
        let newTy = range newTy in
        let (newTy,tyVars) = dest_type newTy in
        let tyVars = map dest_vartype tyVars in
        let () = log_type_op_name newTy in
        let () = log_const_name absTm in
        let () = log_const_name repTm in
        let () = log_list log_type_var tyVars in
        let () = log_thm exists_th in
        let () = log_command "defineTypeOp" in
        let rap_k = save_top () in
        let () = log_command "pop" in
        let arp_k = save_top () in
        let () = log_command "pop" in
        let rep_k = save_top_obj (Object.Const_object repTm) in
        let () = log_command "pop" in
        let abs_k = save_top_obj (Object.Const_object absTm) in
        let () = log_command "pop" in
        let ty_k = save_top_obj (Object.Type_op_object newTy) in
        let () = log_command "pop" in
        (* Derive HOL Light absRepTh from OpenTheory absRepTh *)
        let () = log_term eqTm in
        let () = log_command "refl" in
        let () = log_term (mk_comb (mk_abs (aTm,absRepATm), aTm)) in
        let () = log_command "betaConv" in
        let () = log_command "appThm" in
        let () = log_term (mk_comb (mk_abs (aTm,aTm), aTm)) in
        let () = log_command "betaConv" in
        let () = log_command "appThm" in
        let () = get_saved arp_k in
        let () = log_term aTm in
        let () = log_command "refl" in
        let () = log_command "appThm" in
        let () = log_command "eqMp" in
        let ar_k = save_top_obj (Object.Thm_object ar) in
        let () = log_command "pop" in
        (* Derive HOL Light repAbsTh from OpenTheory repAbsTh *)
        let () = log_term iffTm in
        let () = log_command "refl" in
        let () = log_term (mk_comb (mk_abs (rTm,repAbsREqRTm), rTm)) in
        let () = log_command "betaConv" in
        let () = log_command "appThm" in
        let () = log_term (mk_comb (mk_abs (rTm,predTm), rTm)) in
        let () = log_command "betaConv" in
        let () = log_command "appThm" in
        let () = get_saved rap_k in
        let () = log_term rTm in
        let () = log_command "refl" in
        let () = log_command "appThm" in
        let () = log_command "eqMp" in
        let () = log_command "sym" in
        let ra_k = save_top_obj (Object.Thm_object ra) in
        let () = log_command "pop" in
        (ty_k,abs_k,rep_k,ar_k,ra_k)
    and log_type_op ty =
        let ob = Object.Type_op_object ty in
        if saved ob then () else
        match (peek_type_op_def ty) with
          Some (Type_op_definition tydef) ->
            let (k,_,_,_,_) = log_type_op_def tydef in
            let () = log_num k in
            let () = log_command "ref" in
            ()
        | None ->
            let () = log_type_op_name ty in
            let () = log_command "typeOp" in
            let _ = save_top_obj ob in
            ()
    and log_type ty =
        let ob = Object.Type_object ty in
        if saved ob then () else
        let () =
            if is_type ty then
              let (n,l) = dest_type ty in
              let () = log_type_op n in
              let () = log_list log_type l in
              let () = log_command "opType" in
              ()
            else
              let () = log_type_var (dest_vartype ty) in
              let () = log_command "varType" in
              () in
        let _ = save_top_obj ob in
        ()
    and log_const_def th =
        let (c,tm) = dest_eq (concl th) in
        let (c,_) = dest_const c in
        let () = log_const_name c in
        let () = log_term tm in
        let () = log_command "defineConst" in
        let th_k = save_top_obj (Object.Thm_object th) in
        let () = log_command "pop" in
        let c_k = save_top_obj (Object.Const_object c) in
        let () = log_command "pop" in
        (c_k,th_k)
    and log_const_list_def (((nvs,th),def),i) =
        let () = log_list (log_pair log_const_name log_var) nvs in
        let () = log_thm th in
        let () = log_command "defineConstList" in
        let def_k = save_top_obj (Object.Thm_object def) in
        let () = log_command "pop" in
        let c_ks =
            let rec f l =
                match l with
                  [] -> let () = log_command "pop" in []
                | (c,_) :: l ->
                  let () = log_command "hdTl" in
                  let c_ks = f l in
                  let c_k = save_top_obj (Object.Const_object c) in
                  let () = log_command "pop" in
                  c_k :: c_ks in
            f nvs in
        let c_k = el i c_ks in
        (c_k,def_k)
    and log_const c =
        let ob = Object.Const_object c in
        if saved ob then () else
        match (peek_const_def c) with
          None ->
            let () = log_const_name c in
            let () = log_command "const" in
            let _ = save_top_obj ob in
            ()
        | Some def ->
            match def with
              Const_definition cdef ->
                let (k,_) = log_const_def cdef in
                let () = log_num k in
                let () = log_command "ref" in
                ()
            | Const_list_definition cdef ->
                let (k,_) = log_const_list_def cdef in
                let () = log_num k in
                let () = log_command "ref" in
                ()
            | Abs_type_definition ty ->
              (match (peek_type_op_def ty) with
                 Some (Type_op_definition tydef) ->
                   let (_,k,_,_,_) = log_type_op_def tydef in
                   let () = log_num k in
                   let () = log_command "ref" in
                   ()
               | None ->
                 failwith ("abs const out of type op definition scope: " ^ ty))
            | Rep_type_definition ty ->
              (match (peek_type_op_def ty) with
                 Some (Type_op_definition tydef) ->
                   let (_,_,k,_,_) = log_type_op_def tydef in
                   let () = log_num k in
                   let () = log_command "ref" in
                   ()
               | None ->
                 failwith ("rep const out of type op definition scope: " ^ ty))
    and log_var v =
        let ob = Object.Var_object v in
        if saved ob then () else
        let (n,ty) = dest_var v in
        let () = log_var_name n in
        let () = log_type ty in
        let () = log_command "var" in
        let _ = save_top_obj ob in
        ()
    and log_term tm =
        let ob = Object.Term_object tm in
        if saved ob then () else
        let () =
            if is_const tm then
              let (n,ty) = dest_const tm in
              let () = log_const n in
              let () = log_type ty in
              let () = log_command "constTerm" in
              ()
            else if is_var tm then
              let () = log_var tm in
              let () = log_command "varTerm" in
              ()
            else if is_comb tm then
              let (a,b) = dest_comb tm in
              let () = log_term a in
              let () = log_term b in
              let () = log_command "appTerm" in
              ()
            else
              let (v,b) = dest_abs tm in
              let () = log_var v in
              let () = log_term b in
              let () = log_command "absTerm" in
              () in
        let _ = save_top_obj ob in
        ()
    and log_subst ins = log_object (Object.mk_subst ins)
    and log_thm th =
        let ob = Object.Thm_object th in
        if saved ob then () else
        let () =
            match read_proof th with
            
              Lem_proof 
              | Axiom_proof 
              | Clemma_proof (_) 
              | Ilemma_proof (_)
              -> (*for testing for now, will have to remove LEM later*)
                let () = log_list log_term (hyp th) in
                let () = log_term (concl th) in
                let () = log_command "axiom" in
                ()
            
            | Refl_proof tm ->
              let () = (refl_count := !refl_count + 1) in 
                let () = log_term tm in
                let () = log_command "refl" in
                ()
            | Sym_proof th ->
                let () = (sym_count := !sym_count + 1) in 
                let () = log_thm th in
                let () = log_command "sym" in
                ()
            | Trans_proof (th1,th2) ->
                let () = (trans_count := !trans_count + 1) in 
                let () = log_thm th1 in
                let () = log_thm th2 in
                let () = log_command "trans" in
                ()
            | Mk_comb_proof (th1,th2) ->
                let () = (appthm_count := !appthm_count + 1) in 
                let () = log_thm th1 in
                let () = log_thm th2 in
                let () = log_command "appThm" in
                ()
            | Abs_proof (v1,th2) ->
                let () = (absThm_count := !absThm_count +1) in 
                let () = log_var v1 in
                let () = log_thm th2 in
                let () = log_command "absThm" in
                ()
            | Beta_conv_proof tm ->
                let () = (betaConv_count := !betaConv_count +1) in
                let () = log_term tm in
                let () = log_command "betaConv" in
                ()
            | Assume_proof tm ->
                let () = (assume_count := !assume_count +1) in 
                let () = log_term tm in
                let () = log_command "assume" in
                ()
            | Eq_mp_proof (th1,th2) ->
                let () = (eqmp_count := !eqmp_count + 1) in 
                let () = log_thm th1 in
                let () = log_thm th2 in
                let () = log_command "eqMp" in
                ()
            (* uncommnted by Robert *)
            | Mp_proof (th1,th2) ->
                let () = (mp_count := !mp_count + 1) in 
                let () = log_thm th1 in
                let () = log_thm th2 in
                let () = log_command "mp" in
                ()
            | Disch_proof (a, th) -> 
                let () = (disch_count := !disch_count + 1) in 
                let () = log_term a in 
                let () = log_thm th in 
                let () = log_command "disch" in 
                ()
            | Spec_proof (a, th) -> 
                let () = (spec_count := !spec_count + 1) in 
                let () = log_term a in 
                let () = log_thm th in 
                let () = log_command "spec" in 
                ()
            | Gen_proof (x, th) -> 
                let () = (gen_count := !gen_count + 1) in 
                let () = log_var x in 
                let () = log_thm th in 
                let () = log_command "gen" in 
                () 
            
            | Deduct_antisym_rule_proof (th1,th2) ->
                let () = (deductAntisym_count := !deductAntisym_count +1) in 
                let () = log_thm th1 in
                let () = log_thm th2 in
                let () = log_command "deductAntisym" in
                ()
            | Prove_hyp_proof (th1,th2) ->
                let () = (proveHyp_count := !proveHyp_count +1) in 
                let () = log_thm th1 in
                let () = log_thm th2 in
                let () = log_command "proveHyp" in
                ()
            | Subst_proof (i1,th2) ->
                let () = (subst_count := !subst_count +1) in 
                let () = log_subst i1 in
                let () = log_thm th2 in
                let () = log_command "subst" in
                ()
            | New_basic_definition_proof c ->
                (match (peek_const_def c) with
                   Some (Const_definition cdef) ->
                     let (_,k) = log_const_def cdef in
                     let () = log_num k in
                     let () = log_command "ref" in
                     ()
                 | _ ->
                   failwith ("thm out of const definition scope: " ^ c))
            | New_basic_type_definition_proof (is_ar,ty) ->
                (match (peek_type_op_def ty) with
                   Some (Type_op_definition tydef) ->
                     let (_,_,_,ar_k,ra_k) = log_type_op_def tydef in
                     let () = log_num (if is_ar then ar_k else ra_k) in
                     let () = log_command "ref" in
                     ()
                 | _ ->
                   failwith ("thm out of type op definition scope: " ^ ty))
            | Define_const_list_proof c ->
                (match (peek_const_def c) with
                   Some (Const_list_definition cdef) ->
                     let (_,k) = log_const_list_def cdef in
                     let () = log_num k in
                     let () = log_command "ref" in
                     ()
                 | _ ->
                   failwith ("thm out of const list definition scope: " ^ c)) in
        let _ = save_top_obj ob in
        ()
    and log_object obj =
        if saved obj then () else
        match obj with
          Object.Num_object n -> log_num n
        | Object.Name_object n -> log_name n
        | Object.List_object l -> log_list log_object l
        | Object.Type_op_object t -> log_type_op t
        | Object.Type_object t -> log_type t
        | Object.Const_object c -> log_const c
        | Object.Var_object v -> log_var v
        | Object.Term_object t -> log_term t
        | Object.Thm_object t -> log_thm t in
    (log_term,log_thm,log_clear);;

(* ------------------------------------------------------------------------- *)
(* Article files.                                                            *)
(* ------------------------------------------------------------------------- *)

type article = Article of string * string;;

let the_articles = ref ([] : article list);;

let reset_articles () = the_articles := [];;

let thy_article (Article (thy,_)) = thy;;

let name_article (Article (_,name)) = name;;

let exists_name_article name =
    List.exists (fun art -> name_article art = name) (!the_articles);;

let fresh_name_article thy =
    let rec check i =
        let name = thy ^ "-a" ^ string_of_int i in
        if exists_name_article name then check (i + 1) else name in
    if exists_name_article thy then check 1 else thy;;

let filename_article art =
    "opentheory/articles/" ^ name_article art ^ ".art";;

let add_article thy =
    let name = fresh_name_article thy in
    let art = Article (thy,name) in
    let () = the_articles := art :: !the_articles in
    filename_article art;;

(* ------------------------------------------------------------------------- *)
(* Writing theory files.                                                     *)
(* ------------------------------------------------------------------------- *)

type theory_block =
     Article_theory_block of string
   | Package_theory_block of string
   | Union_theory_block;;

let write_theory_file thy names =
    let int = "" in
    let h = open_out ("opentheory/articles/" ^ thy ^ ".thy") in
    let add_theory_block name imps sint block =
        let () = output_string h ("\n" ^ name ^ " {\n" ^ imps) in
        let () = if sint then output_string h int else () in
        let () =
            match block with
              Article_theory_block file ->
              output_string h ("  article: \"" ^ file ^ "\"\n")
            | Package_theory_block pkg ->
              output_string h ("  package: " ^ pkg ^ "\n")
            | Union_theory_block -> () in
        let () = output_string h "}\n" in
        "  import: " ^ name ^ "\n" in
    let add_article_block imps name =
        let file = name ^ ".art" in
        imps ^ add_theory_block name imps true (Article_theory_block file) in
    let add_union_block name imps =
        add_theory_block name imps false Union_theory_block in
    let () = output_string h ("description: theory file for " ^ thy ^ "\n") in
    let imps = List.fold_left add_article_block "" names in
    let _ = add_union_block "main" imps in
    let () = close_out h in
    ();;

let write_theory_files () =
    let rec write_theories arts =
        match arts with
          [] -> ()
        | art :: arts ->
            let thy = thy_article art in
            let is_thy a = thy_article a = thy in
            let not_thy a = not (is_thy a) in
            let names = map name_article (art :: List.filter is_thy arts) in
            let arts = List.filter not_thy arts in
            let () = write_theory_file thy (rev names) in
            write_theories arts in
    let arts = !the_articles in
    let () = write_theories arts in
    ();;

(* ------------------------------------------------------------------------- *)
(* The current theory.                                                       *)
(* ------------------------------------------------------------------------- *)

let the_current_theory = ref (None : string option);;

let reset_the_current_theory () = the_current_theory := None;;

let set_the_current_theory thy = the_current_theory := Some thy;;

let get_the_current_theory () =
    match !the_current_theory with
      Some thy -> thy
    | None -> failwith "no current theory (use logfile to set)";;

(* ------------------------------------------------------------------------- *)
(* Setting up the log files: part 2                                          *)
(* ------------------------------------------------------------------------- *)

let logfile_end () =
    let () = reset_the_current_theory () in
    match (!log_state) with
      Active_logging (h,_) ->
        let () = log_clear () in
        let () = close_out h in
        let () = log_state := Ready_logging in
        ()
    | _ -> ();;

let logfile thy =
    let () = logfile_end () in
    let () = set_the_current_theory thy in
    match (!log_state) with
      Ready_logging ->
        let file = add_article thy in
        let h = open_out file in
        let ld = new_log_dict true in
        let () = log_state := Active_logging (h,ld) in
        let () = log_num 6 in
        let () = log_command "version" in
        ()
    | _ -> ();;

let is_logging () =
    match (!log_state) with
      Active_logging _ -> true
    | _ -> false;;

let not_logging () = not (is_logging ());;

let start_logging () =
    match (!log_state) with
      Not_logging ->
        let () = reset_articles () in
        let new_log_state =
            let l = log_env () in
            if l = 0 then Not_logging else Ready_logging in
        let () = log_state := new_log_state in
        ()
    | _ -> ();;

let stop_logging () =
    let () = logfile_end () in
    match (!log_state) with
      Ready_logging ->
        let () = write_theory_files () in
        let () = log_state := Not_logging in
        ()
    | _ -> ();;

(* ------------------------------------------------------------------------- *)
(* Tracking exported theorems.                                               *)
(* ------------------------------------------------------------------------- *)

let the_exported_thms =
    ref (Sequent_map.empty : (thm * string) Sequent_map.t);;

let add_the_exported_thms th thy =
    the_exported_thms := add_sequent_map (!the_exported_thms) (th,thy);;

let peek_the_exported_thms seq = peek_sequent_map (!the_exported_thms) seq;;

let list_the_exported_thms () =
    map snd (Sequent_map.bindings (!the_exported_thms));;

(* ------------------------------------------------------------------------- *)
(* Exporting theorems.                                                       *)
(* ------------------------------------------------------------------------- *)

let thm_type_ops =
    let rec type_ops_in_types acc tys =
        match tys with
          [] -> acc
        | ty :: tys ->
          if is_vartype ty then type_ops_in_types acc tys
          else
            let (t,l) = dest_type ty in
            let acc = if List.mem t acc then acc else t :: acc in
            type_ops_in_types acc (l @ tys) in
    let rec type_ops_in_terms acc tms =
        match tms with
          [] -> acc
        | tm :: tms ->
          if is_var tm then
            let (_,ty) = dest_var tm in
            let acc = type_ops_in_types acc [ty] in
            type_ops_in_terms acc tms
          else if is_const tm then
            let (_,ty) = dest_const tm in
            let acc = type_ops_in_types acc [ty] in
            type_ops_in_terms acc tms
          else if is_comb tm then
            let (f,x) = dest_comb tm in
            type_ops_in_terms acc (f :: x :: tms)
          else
            let (v,b) = dest_abs tm in
            type_ops_in_terms acc (v :: b :: tms) in
    fun th -> type_ops_in_terms [] (concl th :: hyp th);;

let thm_consts =
    let rec consts_in_terms acc tms =
        match tms with
          [] -> acc
        | tm :: tms ->
          if is_var tm then consts_in_terms acc tms
          else if is_const tm then
            let (c,_) = dest_const tm in
            let acc = if List.mem c acc then acc else c :: acc in
            consts_in_terms acc tms
          else if is_comb tm then
            let (f,x) = dest_comb tm in
            consts_in_terms acc (f :: x :: tms)
          else
            let (_,b) = dest_abs tm in
            consts_in_terms acc (b :: tms) in
    fun th -> consts_in_terms [] (concl th :: hyp th);;

let debug_export_thm_enable = ref true;;

let export_thm th =
    if not (!debug_export_thm_enable) then () else
    let () =
        if not_logging () then () else
        let () = log_thm th in
        let () = log_list log_term (hyp th) in
        let () = log_term (concl th) in
        let () = log_command "thm" in
        () in
    let () = delete_proof th in
    let () = delete_type_op_definition (thm_type_ops th) in
    let () = delete_const_definition (thm_consts th) in
    let thy = get_the_current_theory () in
    let () = add_the_exported_thms th thy in
    ();;

(* ------------------------------------------------------------------------- *)
(* Exporting proofs.                                                         *)
(* ------------------------------------------------------------------------- *)

let export_proof h th =
    let old_log_state = !log_state in
    let ld = new_log_dict true in
    let () = log_state := Active_logging (h,ld) in
    let () = log_thm th in
    let () = log_list log_term (hyp th) in
    let () = log_term (concl th) in
    let () = log_command "thm" in
    let () = log_clear () in
    let () = log_state := old_log_state in
    ();;

(* ------------------------------------------------------------------------- *)
(* Exporting goals.                                                          *)
(* ------------------------------------------------------------------------- *)

let export_goal file (hs,c) =
    let old_log_state = !log_state in
    let h = open_out file in
    let ld = new_log_dict false in
    let () = log_state := Active_logging (h,ld) in
    let () = log_list log_term hs in
    let () = log_term c in
    let () = log_command "axiom" in
    let () = log_list log_term hs in
    let () = log_term c in
    let () = log_command "thm" in
    let () = log_clear () in
    let () = close_out h in
    let () = log_state := old_log_state in
    ();;

end

let export_goal = Export.export_goal
and export_proof = Export.export_proof
and export_thm = Export.export_thm
and logfile = Export.logfile
and logfile_end = Export.logfile_end
and peek_the_exported_thms = Export.peek_the_exported_thms
and list_the_exported_thms = Export.list_the_exported_thms
and start_logging = Export.start_logging
and stop_logging = Export.stop_logging;;
