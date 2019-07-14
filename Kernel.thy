theory Kernel
  imports Main
begin

section \<open>Task\<close>
subsection \<open>2\<close>
type_synonym ty_name = "char list"

datatype type =
  Ty_Var ty_name ("_:*" [1000] 999) |
  Fun type type (infixr "\<rightarrow>>" 600)

(*test*)
(*
term "''a'':*"
term "''a'':* \<rightarrow>> ''b'':*"
*)


subsection \<open>3\<close>
\<comment> \<open>variable name\<close>
type_synonym name = "nat"

text \<open>
If you want to print terms,
please use following definitions instead
and do so for other functions similarly.
\<close>
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

datatype "term" =
  Var name type ("_::_" 500) |
  Abs name type "term" ("\<lambda>_::_. _>" [1000, 998, 499] 999) |
  App "term" "term" ("|[_ _]|")

(*test*)
(*
term "0::''a'':*"
term "\<lambda>0:: ''a'':*. 0::''a'':*>"
term "|[\<lambda>0:: ''a'':*. 0::''a'':*> 0::''a'':*]|"
*)


subsection \<open>4\<close>
fun type_of :: "term \<Rightarrow> type option" where
  "type_of (Var n t) = Some t" |
  "type_of (Abs n T t) = (case type_of t of
    Some T' \<Rightarrow> Some (Fun T T') |
    None \<Rightarrow> None)" |
  "type_of (App t1 t2) = (case type_of t1 of
    Some (Fun T1 T2) \<Rightarrow> if Some T1 = type_of t2 then Some T2 else None |
    _ \<Rightarrow> None)"

(*test*)
(*
lemma "type_of |[0::''a'':* 1::''b'':*]| = None" by simp
*)

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
    Some (Fun T _) \<Rightarrow>
      let e1 = env_of t1 in
      let e2 = env_of t2 in
      Some T = type_of t2 \<and> (\<forall>n\<in>dom e1 \<inter> dom e2. e1 n = e2 n) \<and>
        well_typed t1 \<and> well_typed t2 |
    _ \<Rightarrow> False)"

(*test*)
(*
lemma "well_typed (0::''a'':* )" by simp
lemma "\<not> well_typed |[0::''a'':* 1::''b'':*]|" by simp
lemma "(0::''a'':* ) \<noteq> undefined" oops
*)

\<comment> \<open>safe term constructors\<close>
definition mk_var :: "name \<Rightarrow> type \<Rightarrow> term option" where
  "mk_var n T = Some (Var n T)"
fun mk_abs :: "name \<Rightarrow> type \<Rightarrow> term option \<Rightarrow> term option" where
  "mk_abs n T (Some t) = (
    let ret = (Abs n T t) in
    if well_typed ret then Some ret else None)" |
  "mk_abs _ _ _ = None"
fun mk_app :: "term option \<Rightarrow> term option \<Rightarrow> term option" where
  "mk_app (Some t1) (Some t2) = (
    let ret = (App t1 t2) in
    if well_typed ret then Some ret else None)" |
  "mk_app _ _ = None"


subsection \<open>5\<close>
\<comment> \<open>user accessible functions\<close>
definition "assume" :: "name \<Rightarrow> type \<Rightarrow> term option" where
  "assume = mk_var"
definition imp_i :: "name \<Rightarrow> type \<Rightarrow> term option \<Rightarrow> term option" where
  "imp_i = mk_abs"
definition imp_e :: "term option \<Rightarrow> term option \<Rightarrow> term option" where
  "imp_e = mk_app"

lemmas mk_def = mk_var_def
lemmas rule_def = assume_def imp_i_def imp_e_def

(*test*)
(*
lemma "imp_i 0 (''a'':* ) (assume 0 (''a'':* )) = Some (\<lambda>0::''a'':*. 0::''a'':*>)"
  by (simp add: mk_def rule_def)
lemma "type_of (the (imp_i 0 (''a'':* ) (imp_i 1 (''a'':* \<rightarrow>> ''b'':* ) (imp_e (assume 1 (''a'':* \<rightarrow>> ''b'':* )) (assume 0 (''a'':* ))))))
  = Some (''a'':* \<rightarrow>> (''a'':* \<rightarrow>> ''b'':* ) \<rightarrow>> ''b'':* )"
  by (simp add: mk_def rule_def)
*)


subsection \<open>6\<close>
definition print :: "term option \<Rightarrow> type \<times> term" where
  "print t = (the (type_of (the t)), the t)"

(*test*)
(*printable version*)
(*
value "print (imp_i X (''a'':* ) (assume X (''a'':* )))"
value "print (
imp_i X (''a'':* \<rightarrow>> ''b'':* \<rightarrow>> ''c'':* ) (
  imp_i Y (''a'':* \<rightarrow>> ''b'':* ) (
    imp_i Z (''a'':* ) (
      imp_e
        (imp_e
          (assume X (''a'':* \<rightarrow>> ''b'':* \<rightarrow>> ''c'':* ))
          (assume Z (''a'':* )))
        (imp_e
          (assume Y (''a'':* \<rightarrow>> ''b'':* ))
          (assume Z (''a'':* )))
))))"
*)


subsection \<open>7\<close>
lemma example: "print (
imp_i 0 (''a'':* \<rightarrow>> ''b'':* \<rightarrow>> ''c'':* ) (
  imp_i 1 (''a'':* \<rightarrow>> ''b'':* ) (
    imp_i 2 (''a'':* ) (
      imp_e
        (imp_e
          (assume 0 (''a'':* \<rightarrow>> ''b'':* \<rightarrow>> ''c'':* ))
          (assume 2 (''a'':* )))
        (imp_e
          (assume 1 (''a'':* \<rightarrow>> ''b'':* ))
          (assume 2 (''a'':* )))
))))
=
((''a'':* \<rightarrow>> ''b'':* \<rightarrow>> ''c'':*) \<rightarrow>> (''a'':* \<rightarrow>> ''b'':*) \<rightarrow>> ''a'':* \<rightarrow>> ''c'':*,
\<lambda>0::(''a'':* \<rightarrow>> ''b'':* \<rightarrow>> ''c'':*). \<lambda>1::(''a'':* \<rightarrow>> ''b'':*). \<lambda>2::''a'':*. |[ |[0::''a'':* \<rightarrow>> ''b'':* \<rightarrow>> ''c'':* 2::''a'':*]| |[1::''a'':* \<rightarrow>> ''b'':* 2::''a'':*]| ]|>>>)"
  by (simp add: print_def rule_def mk_def)





section \<open>Addition\<close>
\<comment> \<open>proof terms\<close>
inductive pr_term :: "term \<Rightarrow> bool" where
  "assume n T = Some t \<Longrightarrow> pr_term t" |
  "pr_term t \<Longrightarrow> imp_i n T (Some t) = Some t' \<Longrightarrow> pr_term t'" |
  "pr_term t1 \<Longrightarrow> pr_term t2 \<Longrightarrow> imp_e (Some t1) (Some t2) = Some t \<Longrightarrow> pr_term t"


theorem soundness: "pr_term t \<Longrightarrow> well_typed t"
proof (induct t rule: pr_term.induct)
  case (1 n T t)
  then show ?case by (auto simp add: rule_def mk_def)
next
  case (2 t n T t')
  then show ?case
    by (smt imp_i_def mk_abs.simps(1) option.distinct(1) option.sel)
next
  case (3 t1 t2 t)
  then show ?case
    by (metis (full_types) imp_e_def mk_app.simps(1) option.distinct(1) option.sel)
qed


theorem completeness: "well_typed t \<Longrightarrow> \<exists>t'. pr_term t' \<and> type_of t' = type_of t \<and> env_of t' = env_of t"
proof (induct t rule: well_typed.induct)
  case (1 n T)
  show ?case
    apply (rule exI[of _ "Var n T"])
    by (simp add: assume_def mk_var_def pr_term.intros(1))
next
  case (2 n T t)
  have "\<exists>t'. pr_term t' \<and> type_of t' = type_of t \<and> env_of t' = env_of t"
    (is "\<exists>t'. ?t' t'")
    apply (rule "2.hyps"[of "env_of t n"])
      apply simp
    using "2.prems"
     apply (meson well_typed.simps(2))
    by (meson "2.prems" well_typed.simps(2))
  then obtain t' where t': "?t' t'" by auto
  show ?case
    apply (rule exI[of _ "\<lambda>n::T. t'>"])
    using t'
    apply auto
    apply (rule pr_term.intros(2)[of t' n T])
    using soundness
     apply (auto simp add: rule_def Let_def)
    by (meson "2.prems" well_typed.simps(2))
next
  case (3 t1 t2)
  have "\<exists>T1 T2. type_of t1 = Some (T1 \<rightarrow>> T2) \<and> type_of t2 = Some T1"
    (is "\<exists>T1 T2. ?type T1 T2")
    using "3.prems"
    apply (rule well_typed.elims(2))
      apply auto
    apply (cases "type_of t1")
     apply simp_all
    apply (rename_tac T)
    apply (case_tac T)
     apply simp_all
    by metis
  then obtain T1 T2 where T1T2: "?type T1 T2" by auto
  have "\<exists>t1' t2'. pr_term t1' \<and> type_of t1' = type_of t1 \<and> env_of t1' = env_of t1 \<and>
    pr_term t2' \<and> type_of t2' = type_of t2 \<and> env_of t2' = env_of t2"
    (is "\<exists>t1' t2'. ?term t1' t2'")
    using "3.hyps"(1)[of "T1 \<rightarrow>> T2"] "3.hyps"(2)[of "T1 \<rightarrow>> T2"] "3.prems" T1T2 by fastforce
  then obtain t1' t2' where t1t2': "?term t1' t2'" by auto
  show ?case
    apply (rule exI[of _ "|[t1' t2']|"])
    using t1t2'
    apply auto
     apply (rule pr_term.intros(3)[of t1' t2'])
       apply (auto simp add: rule_def)
     apply (cases "type_of t1")
    using T1T2
      apply auto
    using soundness "3.prems"
    apply (auto simp add: Let_def)
    done
qed


hide_type (open) "term"
hide_const (open) mk_var
hide_const (open) mk_abs
hide_const (open) mk_app

end
