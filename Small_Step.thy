theory Small_Step imports Star Big_Step begin

inductive small_step :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>" 55) where
  Assign:  "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))"

| Seq1:    "(SKIP;; c\<^sub>2, s) \<rightarrow> (c\<^sub>2, s)"
| Seq2:    "(c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s') \<Longrightarrow> (c\<^sub>1;; c\<^sub>2, s) \<rightarrow> (c\<^sub>1';; c\<^sub>2, s')"

| IfTrue:  "bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> (c\<^sub>1, s)"
| IfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> (c\<^sub>2, s)"

| While:   "(WHILE b DO c, s) \<rightarrow>
            (IF b THEN c;; WHILE b DO c ELSE SKIP, s)"

(* Define the execution of a program as the reflexive transitive
   closure of the small_step judgement using the star operator. *)
abbreviation
  small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y \<equiv> star small_step x y"

(* Execution *)
code_pred small_step .

(* This will "trace" the intermediate program configurations
   while walking the small-step semantics. *)
values "{ (c', map t [''x'',''y'',''z'']) |c' t.
  (''x'' ::= V ''z'';; ''y'' ::= V ''x'', <''x'' := 3, ''y'' := 7, ''z'' := 5>)
  \<rightarrow>* (c',t) }"

lemmas small_step_induct = small_step.induct[split_format(complete)]

(* Proof automation *)
declare small_step.intros[simp, intro]

(* Rule inversion *)
inductive_cases SkipE[elim!]: "(SKIP, s) \<rightarrow> ct"
thm SkipE
inductive_cases AssignE[elim!]: "(x ::= a, s) \<rightarrow> ct"
thm AssignE
inductive_cases SeqE[elim]: "(c\<^sub>1;; c\<^sub>2, s) \<rightarrow> ct"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2, s) \<rightarrow> ct"
inductive_cases WhileE[elim]: "(WHILE b DO c, s) \<rightarrow> ct"

lemma deterministic:
  "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow> cs'' \<Longrightarrow> cs'' = cs'"
  apply(induction arbitrary: cs'' rule: small_step.induct)
  apply blast+
done

(* Equivalence with big-step semantics *)
(* Both directions are proved separately: for any big-step execution,
   there is an equivalent small-step execution and vice versa. *)

(* Lift a \<rightarrow>\<^sup>\<star> derivation into the context of a semicolon. *)
lemma star_seq2: "(c\<^sub>1, s) \<rightarrow>* (c\<^sub>1', s') \<Longrightarrow> (c\<^sub>1;; c\<^sub>2, s) \<rightarrow>* (c\<^sub>1';; c\<^sub>2, s')"
proof(induction rule: star_induct)
  case refl thus ?case by simp
next
  case step
  thus ?case by (metis Seq2 star.step)
qed

lemma seq_comp:
  "\<lbrakk> (c\<^sub>1, s\<^sub>1) \<rightarrow>* (SKIP, s\<^sub>2); (c\<^sub>2, s\<^sub>2) \<rightarrow>* (SKIP, s\<^sub>3) \<rbrakk>
   \<Longrightarrow> (c\<^sub>1;; c\<^sub>2, s\<^sub>1) \<rightarrow>* (SKIP, s\<^sub>3)"
by (blast intro: star.step star_seq2 star_trans)

(* Show that any big-step execution can be simulated
   by a sequence of small steps ending in SKIP. *)

lemma big_to_small:
  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP, t)"
proof (induction rule: big_step.induct)
  fix s show "(SKIP, s) \<rightarrow>* (SKIP, s)" by simp
next
  fix x a s show "(x ::= a, s) \<rightarrow>* (SKIP, s(x := aval a s))" by auto
next
  fix c1 c2 s1 s2 s3
  assume "(c1, s1) \<rightarrow>* (SKIP, s2)" and "(c2, s2) \<rightarrow>* (SKIP, s3)"
  thus "(c1;; c2, s1) \<rightarrow>* (SKIP, s3)" by (rule seq_comp)
next
  fix s::state and b c0 c1 t
  assume "bval b s"
  hence "(IF b THEN c0 ELSE c1, s) \<rightarrow> (c0, s)" by simp
  moreover assume "(c0, s) \<rightarrow>* (SKIP, t)"
  ultimately
  show "(IF b THEN c0 ELSE c1,s) \<rightarrow>* (SKIP, t)" by (metis star.simps)
next
  fix s::state and b c0 c1 t
  assume "\<not>bval b s"
  hence "(IF b THEN c0 ELSE c1, s) \<rightarrow> (c1, s)" by simp
  moreover assume "(c1, s) \<rightarrow>* (SKIP, t)"
  ultimately
  show "(IF b THEN c0 ELSE c1, s) \<rightarrow>* (SKIP, t)" by (metis star.simps)
next
  fix b c and s::state
  assume b: "\<not>bval b s"
  let ?if = "IF b THEN c;; WHILE b DO c ELSE SKIP"
  have "(WHILE b DO c, s) \<rightarrow> (?if, s)" by blast
  moreover have "(?if, s) \<rightarrow> (SKIP, s)" by (simp add: b)
  ultimately show "(WHILE b DO c, s) \<rightarrow>* (SKIP, s)" by (metis star.refl star.step)
next
  fix b c s s' t
  let ?w  = "WHILE b DO c"
  let ?if = "IF b THEN c;; ?w ELSE SKIP"
  assume w: "(?w, s') \<rightarrow>* (SKIP, t)"
  assume c: "(c, s) \<rightarrow>* (SKIP, s')"
  assume b: "bval b s"
  have "(?w, s) \<rightarrow> (?if, s)" by blast
  moreover have "(?if, s) \<rightarrow> (c;; ?w, s)" by (simp add: b)
  moreover have "(c;; ?w, s) \<rightarrow>* (SKIP, t)" by (rule seq_comp[OF c w])
  ultimately show "(WHILE b DO c, s) \<rightarrow>* (SKIP, t)" by (metis star.simps)
qed

(* Automated version of the proof above. *)
lemma  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP, t)"
proof (induction rule: big_step.induct)
  case Skip show ?case by blast
next
  case Assign show ?case by blast
next
  case Seq thus ?case by (blast intro: seq_comp)
next
  case IfTrue thus ?case by (blast intro: star.step)
next
  case IfFalse thus ?case by (blast intro: star.step)
next
  case WhileFalse thus ?case
    by (metis star.step star_step1 small_step.IfFalse small_step.While)
next
  case WhileTrue
  thus ?case
    by (metis While seq_comp small_step.IfTrue star.step[of small_step])
qed

(* The other direction: small-step implies big-step. *)
lemma small1_big_continue:
  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
  apply (induction arbitrary: t rule: small_step.induct)
  apply auto
done

lemma small_to_big:
  "cs \<rightarrow>* (SKIP,t) \<Longrightarrow> cs \<Rightarrow> t"
  apply (induction cs "(SKIP, t)" rule: star.induct)
  apply (auto intro: small1_big_continue)
done

(* Finally, the equivalence theorem: *)
theorem big_iff_small:
  "cs \<Rightarrow> t = cs \<rightarrow>* (SKIP, t)"
by (metis big_to_small small_to_big)

end
