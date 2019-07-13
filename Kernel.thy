theory Kernel
  imports Main
begin

type_synonym ty_name = "char list"

datatype type =
  Ty_Var ty_name ("_:*" [1000] 999) |
  Fun type type (infixr "\<rightarrow>>" 100)

type_synonym name = "nat"
(*printable version*)
(*
datatype name = X | Y | Z | W
fun "next" :: "name \<Rightarrow> name" where
  "next X = Y" |
  "next Y = Z" |
  "next Z = W" |
  "next W = X"
lemma UNIV_name:
  "UNIV = {X, Y, Z, W}"
  by (auto intro: name.exhaust)
instantiation name :: enum
begin
definition
  "enum_name = [X, Y, Z, W]"
definition
  "enum_all_name P \<longleftrightarrow> P X \<and> P Y \<and> P Z \<and> P W"
definition
  "enum_ex_name P \<longleftrightarrow> P X \<or> P Y \<or> P Z \<or> P W"
instance by (intro_classes, auto simp add: enum_name_def enum_all_name_def enum_ex_name_def UNIV_name)
end
*)

(*test*)
\<comment> \<open>
term "''a'':*"
term "''a'':* \<rightarrow>> ''b'':*"
\<close>

datatype "term" =
  Var name type ("_::_" 500) |
  Abs name type "term" ("\<lambda>_:: _. _>" [1000, 998, 499] 999) |
  App "term" "term" ("|[_ _]|")

(*test*)
\<comment> \<open>
term "0::''a'':*"
term "\<lambda>0:: ''a'':*. 0::''a'':*>"
term "|[\<lambda>0:: ''a'':*. 0::''a'':*> 0::''a'':*]|"
\<close>

fun type_of :: "term \<Rightarrow> type" where
  "type_of (Var n t) = t" |
  "type_of (Abs n T t) = Fun T (type_of t)" |
  "type_of (App t1 t2) = (case type_of t1 of
    Fun T1 T2 \<Rightarrow> if T1 = type_of t2 then T2 else undefined)"

(*test*)
\<comment> \<open>
lemma "type_of |[0::''a'':* 1::''b'':*]| = undefined" by simp
\<close>

type_synonym env = "name \<rightharpoonup> type"

fun env_of :: "term \<Rightarrow> env" where
  "env_of (Var n T) = [n \<mapsto> T]" |
  "env_of (Abs n T t) = (env_of t)(n := None)" |
  "env_of (App t1 t2) = env_of t1 ++ env_of t2"

fun well_typed :: "term \<Rightarrow> bool" where
  "well_typed (Var n T) = True" |
  "well_typed (Abs n T t) = (
    let n_Ty = env_of t n in
    if n_Ty = None \<or> n_Ty = Some T then well_typed t else False)" |
  "well_typed (App t1 t2) = (case type_of t1 of
    Fun T _ \<Rightarrow>
      let e1 = env_of t1 in
      let e2 = env_of t2 in
      T = type_of t2 \<and> (\<forall>n\<in>dom e1 \<inter> dom e2. e1 n = e2 n) \<and>
        well_typed t1 \<and> well_typed t2 |
    _ \<Rightarrow> False)"

(*test*)
\<comment> \<open>
lemma "\<not> well_typed |[0::''a'':* 1::''b'':*]|" by simp
\<close>

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

(*user accessible function*)
definition imp_i :: "name \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term" where
  "imp_i = mk_abs"
definition imp_e :: "term \<Rightarrow> term \<Rightarrow> term" where
  "imp_e = mk_app"
definition "assume" :: "name \<Rightarrow> type \<Rightarrow> term" where
  "assume = mk_var"

inductive pr_term where
  "pr_term (assume n T)" |
  "pr_term t \<Longrightarrow> pr_term (imp_i n T t)" |
  "pr_term t1 \<Longrightarrow> pr_term t2 \<Longrightarrow> pr_term (imp_e t1 t2)"

lemma "\<not> well_typed undefined"
(*lemma "pr_term undefined" sledgehammer*)
lemma "\<not> pr_term undefined"

lemmas mk_def = mk_var_def mk_abs_def mk_app_def
lemmas rule_def = imp_i_def imp_e_def assume_def

(*test*)
\<comment> \<open>
lemma "imp_i 0 (''a'':*) (assume 0 (''a'':*)) = (\<lambda>0::''a'':*. 0::''a'':*>)"
  by (simp add: mk_def rule_def)
lemma "type_of (imp_i 0 (''a'':*) (imp_i 1 (''a'':* \<rightarrow>> ''b'':*) (imp_e (assume 1 (''a'':* \<rightarrow>> ''b'':*)) (assume 0 (''a'':*)))))
  = ''a'':* \<rightarrow>> (''a'':* \<rightarrow>> ''b'':*) \<rightarrow>> ''b'':*"
  by (simp add: mk_def rule_def)
\<close>

definition print :: "term \<Rightarrow> type \<times> term" where
  "print t = (type_of t, t)"

(*test*)
\<comment> \<open>
value "print (imp_i X (''a'':*) (assume X (''a'':*)))"
\<close>
\<comment> \<open>
value "print (
imp_i X (''a'':* \<rightarrow>> ''b'':* \<rightarrow>> ''c'':*) (
  imp_i Y (''a'':* \<rightarrow>> ''b'':*) (
    imp_i Z (''a'':*) (
      imp_e
        (imp_e
          (assume X (''a'':* \<rightarrow>> ''b'':* \<rightarrow>> ''c'':*))
          (assume Z (''a'':*)))
        (imp_e
          (assume Y (''a'':* \<rightarrow>> ''b'':*))
          (assume Z (''a'':*)))
))))"
\<close>

theorem soundness: "pr_term t \<Longrightarrow> t \<noteq> undefined \<Longrightarrow> well_typed t"
  by (induct rule: pr_term.induct, auto simp add: mk_def rule_def Let_def)
(*lemma "\<exists>t'. pr_term t' \<and> type_of t' = type_of t \<and> t' \<noteq> undefined"
  apply (cases t)
    apply (metis mk_def rule_def type_of.simps pr_term.simps)
   apply (metis mk_def rule_def type_of.simps pr_term.simps)
  apply (metis mk_def rule_def type_of.simps pr_term.simps)
  done*)
lemma "(a::T:*) \<noteq> undefined"
theorem completeness: "well_typed t \<Longrightarrow> \<exists>t'. pr_term t' \<and> type_of t' = type_of t \<and> t' \<noteq> undefined"
proof (induct t rule: well_typed.induct)
  case (1 n T)
  show ?case
    apply (rule exI[of _ "assume n T"])
    apply (subst pr_term.simps)
    apply auto
     apply (simp add: rule_def mk_def)
    find_theorems undefined
    thm pr_term.simps
next
  case (2 n T t)
  obtain t' where "pr_term t' \<and> type_of t' = type_of t"
  proof -
    have "well_typed t"
      using "2.prems"
      by (meson well_typed.simps(2))
    show ?thesis
      using "2.hyps"[of "Some T"]
      sorry
  qed
  show ?case
    apply (metis mk_def(1) rule_def(3) pr_term.simps type_of.simps)
    apply (rule exI[of _ "imp_i n T t"])
    apply auto
     apply (rule)
    using 2
    apply
    sorry
next
  case (3 t1 t2)
  then show ?case sorry
qed

end
