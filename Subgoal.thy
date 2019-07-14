text \<open>
There is a bug.
In detail, see the comment of fun pr_term_from.
\<close>

theory Subgoal
  imports Kernel
begin

(*todo*)
(*make be more modular*)

type_synonym "prop" = type

type_synonym "subgoal" = "prop list \<times> prop"
definition assms_of :: "subgoal \<Rightarrow> prop list" where "assms_of = fst"
definition thesis_of :: "subgoal \<Rightarrow> prop" where "thesis_of = snd"

datatype inf_rule =
  Assume type |
  Imp_I type |
  Imp_E

\<comment> \<open>derivation tree as inf_rule list\<close>
(*fixme*)
type_synonym deriv_tree = "inf_rule list"

type_synonym pr_state = "subgoal list \<times> deriv_tree"
definition subgoals_of :: "pr_state \<Rightarrow> subgoal list" where "subgoals_of = fst"
definition deriv_tree_of :: "pr_state \<Rightarrow> deriv_tree" where "deriv_tree_of = snd"

definition fresh_var :: "(type \<Rightarrow> name list) \<Rightarrow> name" where
  "fresh_var e = (SOME n. \<forall>T. n \<notin> set (e T))"



datatype method =
  Assumption |
  Rule_Imp_I |
  Rule_Imp_E "prop"
(*future work*)
(*
creating a new rule from theorem
type_synonym method = "subgoal \<Rightarrow> subgoal list"
definition "rule" :: "prop \<Rightarrow> method" where
definition inf_rule_from :: "method \<Rightarrow> inf_rule" where
  "inf_rule_from m = (if m = rule_impI then
    )"
*)


\<comment> \<open>construct proof term from derivation tree\<close>
\<comment> \<open>pr_term_from accumulator_term type_env_as_type_to_nat_list_fun deriv_tree \<Rightarrow> pr_term\<close>
(*fixme*)
text \<open>
There is a bug.
If a variable occurs some times,
then this fun can't create the proof term correctly.
e.g., I can't prove S = \<lambda>x y z. x z (y z): (a \<rightarrow> b \<rightarrow> c) \<rightarrow> (a \<rightarrow> b) \<rightarrow> a \<rightarrow> c,
while I can prove \<lambda>x y z w. x z (y w): (a \<rightarrow> b \<rightarrow> c) \<rightarrow> (a \<rightarrow> b) \<rightarrow> a \<rightarrow> a \<rightarrow> c.
\<close>
fun pr_term_from :: "term option list \<Rightarrow> (type \<Rightarrow> name list) \<Rightarrow> deriv_tree \<Rightarrow> term option list" where
  "pr_term_from ts _ [] = ts" |
  "pr_term_from ts e (r # rs) = (case r of
    Assume T \<Rightarrow> let v = fresh_var e in
      pr_term_from (mk_var v T # ts) (e(T := v # e T)) rs |
    Imp_I T \<Rightarrow> (case e T of
      [] \<Rightarrow> pr_term_from (mk_abs (fresh_var e) T (hd ts) # tl ts) e rs |
      n # ns \<Rightarrow> pr_term_from (mk_abs n T (hd ts) # tl ts) (e(T := ns)) rs) |
    Imp_E \<Rightarrow> (case ts of
      t2 # t1 # ts \<Rightarrow> pr_term_from (mk_app t1 t2 # ts) e rs))"
(*printable version*)
(*
fun pr_term_from :: "term option list \<Rightarrow> (type \<Rightarrow> name list) \<Rightarrow> deriv_tree \<Rightarrow> name \<Rightarrow> term option list" where
  "pr_term_from ts _ [] _ = ts" |
  "pr_term_from ts e (r # rs) i = (case r of
    Assume T \<Rightarrow> let v = i in
      pr_term_from (mk_var v T # ts) (e(T := v # e T)) rs (next i) |
    Imp_I T \<Rightarrow> (case e T of
      [] \<Rightarrow> pr_term_from (mk_abs i T (hd ts) # tl ts) e rs (next i) |
      n # ns \<Rightarrow> pr_term_from (mk_abs n T (hd ts) # tl ts) (e(T := ns)) rs i) |
    Imp_E \<Rightarrow> (case ts of
      t2 # t1 # ts \<Rightarrow> pr_term_from (mk_app t1 t2 # ts) e rs i))"
*)

definition "lemma" :: "prop \<Rightarrow> pr_state" where
  "lemma T = ([([], T)], [])"
definition "apply" :: "pr_state \<Rightarrow> method \<Rightarrow> pr_state" (infixl "apply" 500) where
  "ps apply m = (case subgoals_of ps of sg # sgs \<Rightarrow> (case m of
    Assumption \<Rightarrow> if thesis_of sg \<in> set (assms_of sg) then (sgs, (Assume (thesis_of sg)) # deriv_tree_of ps) else undefined |
    Rule_Imp_I \<Rightarrow> (case thesis_of sg of Fun T1 T2 \<Rightarrow> ((T1 # assms_of sg, T2) # sgs, Imp_I T1 # deriv_tree_of ps)) |
    Rule_Imp_E P \<Rightarrow> ((assms_of sg, Fun P (thesis_of sg)) # (assms_of sg, P) # sgs, Imp_E # deriv_tree_of ps)))"
definition "done" :: "pr_state \<Rightarrow> prop \<times> term" ("_ done" 400) where
  "ps done = (case pr_term_from [] (\<lambda>T. []) (deriv_tree_of ps) of [t] \<Rightarrow> print t)"
(*printable version*)
(*
definition "done" :: "pr_state \<Rightarrow> prop \<times> term" ("_ done" 400) where
  "ps done = (case pr_term_from [] (\<lambda>T. []) (deriv_tree_of ps) X of [t] \<Rightarrow> print t)"
*)



(*test*)
(*printable version*)
(*
value "
lemma (''a'':* \<rightarrow>> ''a'':* )
  apply Rule_Imp_I
  apply Assumption
  done
"
value "
lemma ((''a'':* \<rightarrow>> ''b'':* \<rightarrow>> ''c'':* ) \<rightarrow>> (''a'':* \<rightarrow>> ''b'':* ) \<rightarrow>> ''a'':* \<rightarrow>> ''c'':* )
  apply Rule_Imp_I
  apply Rule_Imp_I
  apply Rule_Imp_I
  apply (Rule_Imp_E (''b'':* ))
  apply (Rule_Imp_E (''a'':* ))
  apply Assumption
  apply Assumption
  apply (Rule_Imp_E (''a'':* ))
  apply Assumption
  apply Assumption
  done
"
*)


(*future work*)
(*
theorem soundness: "\<exists>ms. ((foldl (apply) (lemma l) ms) done) = (T, t) \<Longrightarrow> l = T \<and> T = type_of t \<and> well_typed t"
  sorry
(*inductive provable*)
theorem completeness: "True" ..
*)

end