subsection "Big-Step Operational Semantics of Commands"

theory Big_Step imports Com begin

text \<open>
The big-step semantics is a straight-forward inductive definition
with concrete syntax.
\<close>

(* The big-step rules of IMP *)
inductive big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55) where
  Skip: "       (SKIP, s) \<Rightarrow> s"
| Assign: "     (x ::= a, s) \<Rightarrow> s (x := aval a s)"

| Seq: "        \<lbrakk> (c1, s1) \<Rightarrow> s2; (c2, s2) \<Rightarrow> s3 \<rbrakk> \<Longrightarrow>
                (c1;; c2, s1) \<Rightarrow> s3"

| IfTrue: "     \<lbrakk> bval b s; (c1, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow>
                (IF b THEN c1 ELSE c2, s) \<Rightarrow> t"

| IfFalse: "    \<lbrakk> \<not> bval b s; (c2, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow>
                (IF b THEN c1 ELSE c2, s) \<Rightarrow> t"

| WhileFalse: " \<not> bval b s \<Longrightarrow>
                (WHILE b DO c, s) \<Rightarrow> s"

| WhileTrue: "  \<lbrakk> bval b s1; (c, s1) \<Rightarrow> s2; (WHILE b DO c, s2) \<Rightarrow> s3 \<rbrakk> \<Longrightarrow>
                (WHILE b DO c, s1) \<Rightarrow> s3"

schematic_goal ex: "(''x'' ::= N 5;; ''y'' ::= V ''x'', s) \<Rightarrow> ?t"
apply (rule Seq)
apply (rule Assign)
apply simp
apply (rule Assign)
done

thm ex
thm ex [simplified]

(* We want to execute the big-step rules *)
code_pred big_step.

values "{t. (SKIP, \<lambda>_. 0) \<Rightarrow> t}"
values "{map t [''x''] |t. (SKIP, <''x'' := 42>) \<Rightarrow> t}"
values "{map t [''x''] |t. (''x'' ::= N 2, <''x'' := 42>) \<Rightarrow> t}"
values "{map t [''x'',''y''] |t.
  (WHILE Less (V ''x'') (V ''y'') DO (''x'' ::= Plus (V ''x'') (N 5)),
   <''x'' := 0, ''y'' := 13>) \<Rightarrow> t}"

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

(* Equivalence of commands *)

(* Informally: two commands [c] and [c'] are equivalent with respect
   to the big-step semantics when c started in s terminates in t iff
   c' started in s and also terminates in t. *)
abbreviation equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' \<equiv> (\<forall>s t. (c, s) \<Rightarrow> t = (c', s) \<Rightarrow> t)"

(* Loop unfolding is an equivalence transformation on programs *)
lemma unfold_while:
  "(WHILE b DO c) \<sim> (IF b THEN (c;; WHILE b DO c) ELSE SKIP)" (is "?w \<sim> ?iw")
proof -
  \<comment> \<open>to show the equivalence, we look at the derivation tree for\<close>
  \<comment> \<open>each side and from that construct a derivation tree for the other side\<close>
  have "(?iw, s) \<Rightarrow> t" if assm: "(?w, s) \<Rightarrow> t" for s t
  proof -
    from assm show ?thesis
    proof cases \<comment> \<open>rule inversion on \<open>(?w, s) \<Rightarrow> t\<close>\<close>
      case WhileFalse
      thus ?thesis by blast
    next
      case WhileTrue
      from \<open>bval b s\<close> \<open>(?w, s) \<Rightarrow> t\<close> obtain s' where
        "(c, s) \<Rightarrow> s'" and "(?w, s') \<Rightarrow> t" by auto
      \<comment> \<open>now we can build a derivation tree for the \<^text>\<open>IF\<close>\<close>
      \<comment> \<open>first, the body of the True-branch:\<close>
      hence "(c;; ?w, s) \<Rightarrow> t" by (rule Seq)
      \<comment> \<open>then the whole \<^text>\<open>IF\<close>\<close>
      with \<open>bval b s\<close> show ?thesis by (rule IfTrue)
    qed
  qed
  moreover
  \<comment> \<open>now the other direction:\<close>
  have "(?w, s) \<Rightarrow> t" if assm: "(?iw, s) \<Rightarrow> t" for s t
  proof -
    from assm show ?thesis
    proof cases \<comment> \<open>rule inversion on \<open>(?iw, s) \<Rightarrow> t\<close>\<close>
      case IfFalse
      hence "s = t" using \<open>(?iw, s) \<Rightarrow> t\<close> by blast
      thus ?thesis using \<open>\<not>bval b s\<close> by blast
    next
      case IfTrue
      \<comment> \<open>and for this, only the Seq-rule is applicable:\<close>
      from \<open>(c;; ?w, s) \<Rightarrow> t\<close> obtain s' where
        "(c, s) \<Rightarrow> s'" and "(?w, s') \<Rightarrow> t" by auto
      \<comment> \<open>with this information, we can build a derivation tree for \<^text>\<open>WHILE\<close>\<close>
      with \<open>bval b s\<close> show ?thesis by (rule WhileTrue)
    qed
  qed
  ultimately
  show ?thesis by blast
qed

(* Prove automatically *)
lemma while_unfold:
  "(WHILE b DO c) \<sim> (IF b THEN c;; WHILE b DO c ELSE SKIP)"
by blast

lemma triv_if:
  "(IF b THEN c ELSE c) \<sim> c"
by blast

lemma commute_if:
  "(IF b1 THEN (IF b2 THEN c11 ELSE c12) ELSE c2)
   \<sim>
   (IF b2 THEN (IF b1 THEN c11 ELSE c2) ELSE (IF b1 THEN c12 ELSE c2))"
by blast

lemma sim_while_cong_aux:
  "(WHILE b DO c, s) \<Rightarrow> t \<Longrightarrow> c \<sim> c' \<Longrightarrow> (WHILE b DO c', s) \<Rightarrow> t"
apply(induction "WHILE b DO c" s t arbitrary: b c rule: big_step_induct)
  apply blast
apply blast
done

(* Establishes that \<sim> is a congruence relation w.r.t. WHILE *)
lemma sim_while_cong: "c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b DO c'"
by (metis sim_while_cong_aux)

text \<open>Command equivalence is an equivalence relation, i.e. it is
reflexive, symmetric, and transitive. Because we used an abbreviation
above, Isabelle derives this automatically.\<close>

lemma sim_refl:  "c \<sim> c" by simp
lemma sim_sym:   "(c \<sim> c') = (c' \<sim> c)" by auto
lemma sim_trans: "c \<sim> c' \<Longrightarrow> c' \<sim> c'' \<Longrightarrow> c \<sim> c''" by auto

(* Determinism *)
(* A language is deterministic if any two executions of the
   same command from the same initial state will arrive in the
   same final state. *)

theorem big_step_determ: "\<lbrakk> (c,s) \<Rightarrow> t; (c,s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
  by (induction arbitrary: u rule: big_step.induct) blast+

(* In Isar: *)
theorem
  "(c,s) \<Rightarrow> t  \<Longrightarrow>  (c,s) \<Rightarrow> t'  \<Longrightarrow>  t' = t"
proof (induction arbitrary: t' rule: big_step.induct)
  \<comment> \<open>the only interesting case, \<^text>\<open>WhileTrue\<close>:\<close>
  fix b c s s\<^sub>1 t t'
  \<comment> \<open>The assumptions of the rule:\<close>
  assume "bval b s" and "(c,s) \<Rightarrow> s\<^sub>1" and "(WHILE b DO c,s\<^sub>1) \<Rightarrow> t"
  \<comment> \<open>Ind.Hyp; note the \<^text>\<open>\<And>\<close> because of arbitrary:\<close>
  assume IHc: "\<And>t'. (c,s) \<Rightarrow> t' \<Longrightarrow> t' = s\<^sub>1"
  assume IHw: "\<And>t'. (WHILE b DO c,s\<^sub>1) \<Rightarrow> t' \<Longrightarrow> t' = t"
  \<comment> \<open>Premise of implication:\<close>
  assume "(WHILE b DO c,s) \<Rightarrow> t'"
  with \<open>bval b s\<close> obtain s\<^sub>1' where
      c: "(c,s) \<Rightarrow> s\<^sub>1'" and
      w: "(WHILE b DO c,s\<^sub>1') \<Rightarrow> t'"
    by auto
  from c IHc have "s\<^sub>1' = s\<^sub>1" by blast
  with w IHw show "t' = t" by blast
qed blast+ \<comment> \<open>prove the rest automatically\<close>

end
