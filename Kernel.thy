theory Kernel
  imports Main
begin

type_synonym name = "nat"
type_synonym ty_name = "char list"

datatype type =
  Ty_Var ty_name ("_:*" [1000] 999) |
  Fun type type (infixr "\<rightarrow>>" 100)

term "''a'':*"
term "''a'':* \<rightarrow>> ''b'':*"

datatype "term" =
  Var name type ("_::_" 500) |
  Abs name type "term" ("\<lambda>_:: _. _>" [1000, 998, 499] 999) |
  App "term" "term" ("|[_ _]|")
term "0::''a'':*"
term "\<lambda>0:: ''a'':*. 0::''a'':*>"
term "|[\<lambda>0:: ''a'':*. 0::''a'':*> 0::''a'':*]|"
(*
(*free variable*)
fun fv :: "term \<Rightarrow> name set" where
  "fv (Var n T) = {n}" |
  "fv (Abs n T t) = fv t - {n}" |
  "fv (App t1 t2) = fv t1 \<union> fv t2"
*)
fun type_of :: "term \<Rightarrow> type" where
  "type_of (Var n t) = t" |
  "type_of (Abs n T t) = Fun T (type_of t)" |
  "type_of (App t1 t2) = (case type_of t1 of
    Fun T1 T2 \<Rightarrow> if T1 = type_of t2 then T2 else undefined)"
(*
lemma "type_of (App (Var 0 (Ty_Var ''a'')) (Var 1 (Ty_Var ''b''))) = undefined" by simp
*)
type_synonym env = "name \<rightharpoonup> type"

fun env_of :: "term \<Rightarrow> env" where
  "env_of (Var n T) = [n \<mapsto> T]" |
  "env_of (Abs n T t) = (env_of t)(n := None)" |
  "env_of (App t1 t2) = env_of t1 ++ env_of t2"

fun well_typed where
  "well_typed (Var n T) = True" |
  "well_typed (Abs n T t) = (
    let n_Ty = env_of t n in
    if n_Ty \<in> {None, Some T} then well_typed t else False)" |
  "well_typed (App t1 t2) = (case type_of t1 of
    Fun T _ \<Rightarrow>
      let e1 = env_of t1 in
      let e2 = env_of t2 in
      T = type_of t2 \<and> (\<forall>n\<in>dom e1 \<inter> dom e2. e1 n = e2 n) \<and>
        well_typed t1 \<and> well_typed t2 |
    _ \<Rightarrow> False)"

lemma "\<not> well_typed (App (0::''a'':*) (1::''b'':*))"
  by simp

definition mk_var :: "name \<Rightarrow> type \<Rightarrow> term" where
  "mk_var n T = Var n T"
definition mk_abs :: "name \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term" where
  "mk_abs n T t = (
    let ret = (Abs n T t) in
    if well_typed ret then ret else undefined)"
definition mk_app :: "term \<Rightarrow> term \<Rightarrow> term" where
  "mk_app t1 t2 = (
    let ret = (App t1 t2) in
    if well_typed ret then ret else undefined)"

definition imp_i :: "name \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term" where
  "imp_i = mk_abs"
definition imp_e :: "term \<Rightarrow> term \<Rightarrow> term" where
  "imp_e = mk_app"
definition "assume" :: "name \<Rightarrow> type \<Rightarrow> term" where
  "assume = mk_var"
find_theorems undefined
inductive pr_term where
  "pr_term (assume n T)" |
  "pr_term t \<Longrightarrow> pr_term (imp_i n T t)" |
  "pr_term t1 \<Longrightarrow> pr_term t2 \<Longrightarrow> pr_term (imp_e t1 t2)"

lemmas mk_def = mk_var_def mk_abs_def mk_app_def
lemmas rule_def = imp_i_def imp_e_def assume_def

lemma "pr_term t \<Longrightarrow> t \<noteq> undefined \<Longrightarrow> well_typed t"
  by (induct rule: pr_term.induct, auto simp add: mk_def rule_def Let_def)
(*
lemma "impI ''x'' (Ty_Var ''a'') (assume ''x'' (Ty_Var ''a'')) = (Abs ''x'' (Ty_Var ''a'') (Var ''x'' (Ty_Var ''a'')))"
  by (simp add: mk_def rule_def)
lemma "impI ''x'' ()"
lemma "impI 0 (Ty_Var 1) ()"
lemma "type_of (impI 0 (Ty_Var 2) (impI 1 (Fun (Ty_Var 2) (Ty_Var 3)) (impE (assume 1 (Fun (Ty_Var 2) (Ty_Var 3))) (assume 0 (Ty_Var 2)))))
 = Fun (Ty_Var 2) (Fun (Fun (Ty_Var 2) Ty_Var 3) (Ty_Var 3))"
*)

end
