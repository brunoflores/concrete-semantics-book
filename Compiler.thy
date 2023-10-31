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
| MUL
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
  "iexec instr (i,s,stk) =
    (case instr of
       LOADI n \<Rightarrow> (i+1, s, n # stk)
     | LOAD x \<Rightarrow> (i+1, s, s x # stk)
     | ADD \<Rightarrow> (i+1, s, (hd2 stk + hd stk) # tl2 stk)
     | MUL \<Rightarrow> (i+1, s, (hd2 stk * hd stk) # tl2 stk)
     | STORE x \<Rightarrow> (i+1, s(x := hd stk), tl stk)
     | JMP n \<Rightarrow>  (i+1+n, s, stk)
     | JMPLESS n \<Rightarrow> (if hd2 stk < hd stk then i+1+n else i+1, s, tl2 stk)
     | JMPGE n \<Rightarrow> (if hd2 stk >= hd stk then i+1+n else i+1, s, tl2 stk))"

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

(* To argue about the execution of code that is embedded in
   larger programs, show that execution results are preserved if we append
   additional code to the left or right of a program. *)
lemma iexec_shift [simp]:
  "((n+i', s', stk') = iexec x (n+i, s, stk)) = ((i', s', stk') = iexec x (i, s, stk))"
by (auto split: instr.split)

lemma exec1_appendR: "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P@P' \<turnstile> c \<rightarrow> c'"
by (auto simp: exec1_def)

lemma exec_appendR: "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> P@P' \<turnstile> c \<rightarrow>* c'"
by (induction rule: star.induct) (fastforce intro: star.step exec1_appendR)+

lemma exec1_appendL:
  fixes i i' :: int
  shows
  "P \<turnstile> (i, s, stk) \<rightarrow> (i', s', stk') \<Longrightarrow>
   P' @ P \<turnstile> (size(P')+i, s, stk) \<rightarrow> (size(P')+i', s', stk')"
unfolding exec1_def
by (auto simp del: iexec.simps)

lemma exec_appendL:
  fixes i i' :: int
  shows
  "P \<turnstile> (i, s, stk) \<rightarrow>* (i', s', stk')  \<Longrightarrow>
   P' @ P \<turnstile> (size(P')+i, s, stk) \<rightarrow>* (size(P')+i', s', stk')"
by (induction rule: exec_induct) (blast intro: star.step exec1_appendL)+

text\<open>Now we specialise the above lemmas to enable automatic proofs of
\<^prop>\<open>P \<turnstile> c \<rightarrow>* c'\<close> where \<open>P\<close> is a mixture of concrete instructions and
pieces of code that we already know how they execute (by induction), combined
by \<open>@\<close> and \<open>#\<close>. Backward jumps are not supported.
The details should be skipped on a first reading.

If we have just executed the first instruction of the program, drop it:\<close>

lemma exec_Cons_1 [intro]:
  "P \<turnstile> (0, s, stk) \<rightarrow>* (j, t, stk') \<Longrightarrow>
  instr # P \<turnstile> (1, s, stk) \<rightarrow>* (1+j, t, stk')"
by (drule exec_appendL[where P'="[instr]"]) simp

lemma exec_appendL_if [intro]:
  fixes i i' j :: int
  shows
  "size P' <= i \<Longrightarrow>
   P \<turnstile> (i - size P', s, stk) \<rightarrow>* (j, s', stk') \<Longrightarrow>
   i' = size P' + j \<Longrightarrow>
   P' @ P \<turnstile> (i, s, stk) \<rightarrow>* (i', s', stk')"
by (drule exec_appendL[where P'=P']) simp

(* Split the execution of a compound program up into the execution of its
   parts. *)
lemma exec_append_trans [intro]:
  fixes i' i'' j'' :: int
  shows
  "P \<turnstile> (0, s, stk) \<rightarrow>* (i', s', stk') \<Longrightarrow>
   size P \<le> i' \<Longrightarrow>
   P' \<turnstile>  (i' - size P, s', stk') \<rightarrow>* (i'', s'', stk'') \<Longrightarrow>
   j'' = size P + i'' \<Longrightarrow>
   P @ P' \<turnstile> (0, s, stk) \<rightarrow>* (j'', s'', stk'')"
by (metis star_trans[OF exec_appendR exec_appendL_if])

declare Let_def [simp]

(* Compilation *)

(* Arithmetic expressions *)
fun acomp :: "aexp \<Rightarrow> instr list" where
  "acomp (N n) = [LOADI n]"
| "acomp (V x) = [LOAD x]"
| "acomp (Plus a1 a2) = acomp a1 @ acomp a2 @ [ADD]"
| "acomp (Times a1 a2) = acomp a1 @ acomp a2 @ [MUL]"

lemma acomp_correct [intro]:
  "acomp a \<turnstile> (0, s, stk) \<rightarrow>* (size(acomp a), s, (aval a s) # stk)"
by (induction a arbitrary: stk) fastforce+

end
