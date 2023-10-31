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
inductive_cases SeqE[elim]: "(c1;; c2, s) \<rightarrow> ct"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2, s) \<rightarrow> ct"
inductive_cases WhileE[elim]: "(WHILE b DO c, s) \<rightarrow> ct"

lemma deterministic:
  "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow> cs'' \<Longrightarrow> cs'' = cs'"
  apply(induction arbitrary: cs'' rule: small_step.induct)
  apply blast+
done

end
