theory Compiler imports Big_Step Star begin

(* Preliminaries *)

declare [[coercion_enabled]]
declare [[coercion "int :: nat \<Rightarrow> int"]]

fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
  "(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))"

lemma inth_append [simp]:
  "0 \<le> i \<Longrightarrow>
  (xs @ ys) !! i = (if i < size xs then xs !! i else ys !! (i - size xs))"
by (induction xs arbitrary: i) (auto simp: algebra_simps)

(* Hide coercion int applied to length: *)
abbreviation (output) "isize xs \<equiv> int (length xs)"
notation isize ("size")

(* The machine itself *)
(* Realistically, we would map variable names to memory locations. *)

datatype instr =
  LOADI int
| LOAD vname
| ADD
| STORE vname
| JMP int
| JMPLESS int (* Compare two topmost stack elements and jump if
                 the second one is less. *)
| JMPGE int   (* Compare two topmost stack elements and jump if
                 the second one is greater or equal. *)

(* Program configurations *)
type_synonym stack = "val list"
type_synonym config = "int \<times> state \<times> stack"

abbreviation "hd2 xs == hd(tl xs)"
abbreviation "tl2 xs == tl(tl xs)"

fun iexec :: "instr \<Rightarrow> config \<Rightarrow> config" where
  "iexec (LOADI n) (i, s, stk)   = (i + 1, s, n # stk)"
| "iexec (LOAD x) (i, s, stk)    = (i +1, s, s x # stk)"
| "iexec ADD (i, s, stk)         = (i + 1, s, (hd2 stk + hd stk) # tl2 stk)"
| "iexec (STORE x) (i, s, stk)   = (i + 1, s(x := hd stk), tl stk)"
| "iexec (JMP n) (i, s, stk)     = (i + 1 + n, s, stk)"
| "iexec (JMPLESS n) (i, s, stk) = (if hd2 stk < hd stk then i + 1 + n else i + 1, s, tl2 stk)"
| "iexec (JMPGE n) (i, s, stk)   = (if hd stk \<le> hd2 stk then i + 1 + n else i + 1, s, tl2 stk)"

definition exec1 :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("(_/ \<turnstile> (_ \<rightarrow>/ _))" [59,0,59] 60)
where
  "P \<turnstile> c \<rightarrow> c' =
  (\<exists>i s stk. c = (i, s, stk) \<and> c' = iexec (P!!i) (i, s, stk) \<and> 0 \<le> i \<and> i < size P)"

lemma exec1I [intro, code_pred_intro]:
  "c' = iexec (P!!i) (i, s, stk) \<Longrightarrow> 0 \<le> i \<Longrightarrow> i < size P \<Longrightarrow>
   P \<turnstile> (i, s, stk) \<rightarrow> c'"
by (simp add: exec1_def)

abbreviation
  exec :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("(_/ \<turnstile> (_ \<rightarrow>*/ _))" 50)
where
  "exec P \<equiv> star (exec1 P)"

lemmas exec_induct = star.induct [of "exec1 P", split_format(complete)]

code_pred exec1 by (metis exec1_def)

values
  "{(i, map t [''x'',''y''], stk) | i t stk.
    [LOAD ''y'', STORE ''x''] \<turnstile>
    (0, <''x'' := 3, ''y'' := 4>, []) \<rightarrow>* (i, t, stk)}"

(* Show that execution results are preserved if we append
   additional code to the left or right of a program. *)
lemma iexec_shift [simp]:
  "((n+i', s', stk') = iexec x (n+i, s, stk)) = ((i', s', stk') = iexec x (i, s, stk))"
by (auto split: instr.split)

lemma exec1_appendR: "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P@P' \<turnstile> c \<rightarrow> c'"
by (auto simp: exec1_def)

lemma exec_appendR: "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> P@P' \<turnstile> c \<rightarrow>* c'"
by (induction rule: star.induct) (fastforce intro: star.step exec1_appendR)+

end
