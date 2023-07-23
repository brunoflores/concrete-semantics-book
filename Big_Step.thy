subsection "Big-Step Operational Semantics of Commands"

theory Big_Step imports Com begin

text "The big-step semantics is a straight-forward inductive definition with concrete syntax."

inductive big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55) where

  Skip: "(SKIP, s) \<Rightarrow> s"

| Assign: "(x ::= a, s) \<Rightarrow> s (x := aval a s)"

| Seq: "\<lbrakk>(c1, s1) \<Rightarrow> s2; (c1, s2) \<Rightarrow> s3\<rbrakk> \<Longrightarrow>
        (c1;; c2, s1) \<Rightarrow> s3"

| IfTrue: "\<lbrakk>bval b s; (c1, s) \<Rightarrow> t\<rbrakk> \<Longrightarrow>
           (IF b THEN c1 ELSE c2, s) \<Rightarrow> t"

| IfFalse: "\<lbrakk>\<not>bval b s; (c2, s) \<Rightarrow> t\<rbrakk> \<Longrightarrow>
            (IF b THEN c1 ELSE c2, s) \<Rightarrow> t"

| WhileFalse: "\<not>bval b s \<Longrightarrow>
               (WHILE b DO c, s) \<Rightarrow> s"

| WhileTrue: "\<lbrakk>bval b s; (c, s1) \<Rightarrow> s2; (WHILE b DO c, s2) \<Rightarrow> s3\<rbrakk> \<Longrightarrow>
              (WHILE b DO c, s1) \<Rightarrow> s3"

schematic_goal ex: "(''x'' ::= N 5;; ''y'' ::= V ''x'', s) \<Rightarrow> ?t"
apply (rule Seq)
apply (rule Assign)
apply simp
apply (rule Assign)
done

thm ex [simplified]

code_pred big_step.

(* These didn't work:
values "{map t [''x''] |t. (SKIP, <''x'' := 42>) \<Rightarrow> t}"
values "{t. (SKIP, \<lambda>_. 0) \<Rightarrow> t}"
*)

declare big_step.intros [intro]
thm big_step.induct

lemmas big_step_induct = big_step.induct [split_format(complete)]
thm big_step.induct

subsection "Rule Inversion"

(* Elimination rules: *)

inductive_cases SkipE [elim!]: "(SKIP, s) \<Rightarrow> t"
thm SkipE

inductive_cases AssignE [elim!]: "(x ::= a, s) \<Rightarrow> t"
thm AssignE

inductive_cases SeqE [elim!]: "(c1;; c2, s1) \<Rightarrow> s3"
thm SeqE

inductive_cases IfE [elim!]: "(IF b THEN c1 ELSE c2, s) \<Rightarrow> t"
thm IfE

inductive_cases WhileE [elim]: "(WHILE b DO c, s) \<Rightarrow> t"
thm WhileE

(* Automatic example: *)
lemma "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t \<Longrightarrow> t = s"
by blast

(* Rule inversion by hand via the cases method: *)
lemma
  assumes "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t"
  shows "t = s"
proof -
  from assms show ?thesis
  proof cases
    case IfTrue thm IfTrue
    thus ?thesis by blast
  next
    case IfFalse thus ?thesis by blast
  qed
qed

(* Using rule inversion to prove simplification rules: *)
lemma assign_simp:
  "(x ::= a, s) \<Rightarrow> s' \<longleftrightarrow> (s' = s (x := aval a s))"
by auto

text \<open>An example combining rule inversion and derivations\<close>
lemma Seq_assoc:
  "(c1;; c2;; c3, s) \<Rightarrow> s' \<longleftrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> s'"
proof
  assume "(c1;; c2;; c3, s) \<Rightarrow> s'"
  then obtain s1 s2 where
    c1: "(c1, s) \<Rightarrow> s1" and
    c2: "(c2, s1) \<Rightarrow> s2" and
    c3: "(c3, s2) \<Rightarrow> s'" by auto
  from c2 c3
  have "(c2;; c3, s1) \<Rightarrow> s'" by (rule Seq)
  with c1
  show "(c1;; (c2;; c3), s) \<Rightarrow> s'" by (rule Seq)
next
  assume "(c1;; (c2;; c3), s) \<Rightarrow> s'"
  thus "(c1;; c2;; c3, s) \<Rightarrow> s'" by auto
qed

end
