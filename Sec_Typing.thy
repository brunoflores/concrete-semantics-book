theory Sec_Typing imports Sec_Type_Expr begin

(* Syntax directed typing *)

(* We write l \<turnstile> c to mean that command c contains no information flows to
   variables lower than level l, and only safe flows to variables \<ge> l. *)
inductive sec_type :: "nat \<Rightarrow> com \<Rightarrow> bool" ("(_/ \<turnstile> _)" [0, 0] 50) where
  Skip:   "l \<turnstile> SKIP"
| Assign: "\<lbrakk> sec x \<ge> sec a; sec x \<ge> l \<rbrakk> \<Longrightarrow> l \<turnstile> x ::= a"
| Seq:    "\<lbrakk> l \<turnstile> c\<^sub>1; l \<turnstile> c\<^sub>2 \<rbrakk> \<Longrightarrow> l \<turnstile> c\<^sub>1;; c\<^sub>2"
| If:     "\<lbrakk> max (sec b) l \<turnstile> c\<^sub>1; max (sec b) l \<turnstile> c\<^sub>2 \<rbrakk> \<Longrightarrow> l \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2"
| While:  "max (sec b) l \<turnstile> c \<Longrightarrow> l \<turnstile> WHILE b DO c"

code_pred (expected_modes: i \<Rightarrow> i \<Rightarrow> bool) sec_type .

value "0 \<turnstile> IF Less (V ''x1'') (V ''x'') THEN ''x1'' ::= N 0 ELSE SKIP"
value "1 \<turnstile> IF Less (V ''x1'') (V ''x'') THEN ''x''  ::= N 0 ELSE SKIP"
value "2 \<turnstile> IF Less (V ''x1'') (V ''x'') THEN ''x1'' ::= N 0 ELSE SKIP"

inductive_cases [elim!]:
  "l \<turnstile> x ::= a"  "l \<turnstile> c\<^sub>1;;c\<^sub>2"  "l \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2"  "l \<turnstile> WHILE b DO c"

end
