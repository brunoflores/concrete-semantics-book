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

end
