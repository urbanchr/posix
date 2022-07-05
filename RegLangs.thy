theory RegLangs
  imports Main "HOL-Library.Sublist"
begin

section \<open>Sequential Composition of Languages\<close>

definition
  Sequ :: "string set \<Rightarrow> string set \<Rightarrow> string set" ("_ ;; _" [100,100] 100)
where 
  "A ;; B = {s1 @ s2 | s1 s2. s1 \<in> A \<and> s2 \<in> B}"

text \<open>Two Simple Properties about Sequential Composition\<close>

lemma Sequ_empty_string [simp]:
  shows "A ;; {[]} = A"
  and   "{[]} ;; A = A"
by (simp_all add: Sequ_def)

lemma Sequ_empty [simp]:
  shows "A ;; {} = {}"
  and   "{} ;; A = {}"
  by (simp_all add: Sequ_def)

lemma concI[simp,intro]: "u : A \<Longrightarrow> v : B \<Longrightarrow> u@v : A ;; B"
by (auto simp add: Sequ_def)

lemma concE[elim]: 
assumes "w \<in> A ;; B"
obtains u v where "u \<in> A" "v \<in> B" "w = u@v"
using assms by (auto simp: Sequ_def)

lemma concI_if_Nil2: "[] \<in> B \<Longrightarrow> xs : A \<Longrightarrow> xs \<in> A ;; B"
by (metis append_Nil2 concI)

lemma conc_assoc: "(A ;; B) ;; C = A ;; (B ;; C)"
by (auto elim!: concE) (simp only: append_assoc[symmetric] concI)


text \<open>Language power operations\<close>

overloading lang_pow == "compow :: nat \<Rightarrow> string set \<Rightarrow> string set"
begin
  primrec lang_pow :: "nat \<Rightarrow> string set \<Rightarrow> string set" where
  "lang_pow 0 A = {[]}" |
  "lang_pow (Suc n) A = A ;; (lang_pow n A)"
end


lemma conc_pow_comm:
  shows "A ;; (A ^^ n) = (A ^^ n) ;; A"
by (induct n) (simp_all add: conc_assoc[symmetric])

lemma lang_pow_add: "A ^^ (n + m) = (A ^^ n) ;; (A ^^ m)"
  by (induct n) (auto simp: conc_assoc)

lemma lang_empty: 
  fixes A::"string set"
  shows "A ^^ 0 = {[]}"
  by simp

section \<open>Semantic Derivative (Left Quotient) of Languages\<close>

definition
  Der :: "char \<Rightarrow> string set \<Rightarrow> string set"
where
  "Der c A \<equiv> {s. c # s \<in> A}"

definition
  Ders :: "string \<Rightarrow> string set \<Rightarrow> string set"
where
  "Ders s A \<equiv> {s'. s @ s' \<in> A}"

lemma Der_null [simp]:
  shows "Der c {} = {}"
unfolding Der_def
by auto

lemma Der_empty [simp]:
  shows "Der c {[]} = {}"
unfolding Der_def
by auto

lemma Der_char [simp]:
  shows "Der c {[d]} = (if c = d then {[]} else {})"
unfolding Der_def
by auto

lemma Der_union [simp]:
  shows "Der c (A \<union> B) = Der c A \<union> Der c B"
unfolding Der_def
by auto

lemma Der_Sequ [simp]:
  shows "Der c (A ;; B) = (Der c A) ;; B \<union> (if [] \<in> A then Der c B else {})"
unfolding Der_def Sequ_def
by (auto simp add: Cons_eq_append_conv)


section \<open>Kleene Star for Languages\<close>

inductive_set
  Star :: "string set \<Rightarrow> string set" ("_\<star>" [101] 102)
  for A :: "string set"
where
  start[intro]: "[] \<in> A\<star>"
| step[intro]:  "\<lbrakk>s1 \<in> A; s2 \<in> A\<star>\<rbrakk> \<Longrightarrow> s1 @ s2 \<in> A\<star>"

(* Arden's lemma *)

lemma Star_cases:
  shows "A\<star> = {[]} \<union> A ;; A\<star>"
unfolding Sequ_def
by (auto) (metis Star.simps)

lemma Star_decomp: 
  assumes "c # x \<in> A\<star>" 
  shows "\<exists>s1 s2. x = s1 @ s2 \<and> c # s1 \<in> A \<and> s2 \<in> A\<star>"
using assms
by (induct x\<equiv>"c # x" rule: Star.induct) 
   (auto simp add: append_eq_Cons_conv)

lemma Star_Der_Sequ: 
  shows "Der c (A\<star>) \<subseteq> (Der c A) ;; A\<star>"
unfolding Der_def Sequ_def
by(auto simp add: Star_decomp)

lemma Der_inter[simp]:   "Der a (A \<inter> B) = Der a A \<inter> Der a B"
  and Der_compl[simp]:   "Der a (-A) = - Der a A"
  and Der_Union[simp]:   "Der a (Union M) = Union(Der a ` M)"
  and Der_UN[simp]:      "Der a (UN x:I. S x) = (UN x:I. Der a (S x))"
by (auto simp: Der_def)

lemma Der_star[simp]:
  shows "Der c (A\<star>) = (Der c A) ;; A\<star>"
proof -    
  have "Der c (A\<star>) = Der c ({[]} \<union> A ;; A\<star>)"  
    by (simp only: Star_cases[symmetric])
  also have "... = Der c (A ;; A\<star>)"
    by (simp only: Der_union Der_empty) (simp)
  also have "... = (Der c A) ;; A\<star> \<union> (if [] \<in> A then Der c (A\<star>) else {})"
    by simp
  also have "... =  (Der c A) ;; A\<star>"
    using Star_Der_Sequ by auto
  finally show "Der c (A\<star>) = (Der c A) ;; A\<star>" .
qed

lemma Der_pow[simp]:
  shows "Der c (A ^^ n) = (if n = 0 then {} else (Der c A) ;; (A ^^ (n - 1)))"
  apply(induct n arbitrary: A)
   apply(auto simp add: Cons_eq_append_conv)
  by (metis Suc_pred concI_if_Nil2 conc_assoc conc_pow_comm lang_pow.simps(2))


lemma Star_concat:
  assumes "\<forall>s \<in> set ss. s \<in> A"  
  shows "concat ss \<in> A\<star>"
using assms by (induct ss) (auto)

lemma Star_split:
  assumes "s \<in> A\<star>"
  shows "\<exists>ss. concat ss = s \<and> (\<forall>s \<in> set ss. s \<in> A \<and> s \<noteq> [])"
using assms
  apply(induct rule: Star.induct)
  using concat.simps(1) apply fastforce
  apply(clarify)
  by (metis append_Nil concat.simps(2) set_ConsD)




section \<open>Regular Expressions\<close>

datatype rexp =
  ZERO
| ONE
| CH char
| SEQ rexp rexp
| ALT rexp rexp
| STAR rexp
| NTIMES rexp nat

section \<open>Semantics of Regular Expressions\<close>
 
fun
  L :: "rexp \<Rightarrow> string set"
where
  "L (ZERO) = {}"
| "L (ONE) = {[]}"
| "L (CH c) = {[c]}"
| "L (SEQ r1 r2) = (L r1) ;; (L r2)"
| "L (ALT r1 r2) = (L r1) \<union> (L r2)"
| "L (STAR r) = (L r)\<star>"
| "L (NTIMES r n) = (L r) ^^ n"

section \<open>Nullable, Derivatives\<close>

fun
 nullable :: "rexp \<Rightarrow> bool"
where
  "nullable (ZERO) = False"
| "nullable (ONE) = True"
| "nullable (CH c) = False"
| "nullable (ALT r1 r2) = (nullable r1 \<or> nullable r2)"
| "nullable (SEQ r1 r2) = (nullable r1 \<and> nullable r2)"
| "nullable (STAR r) = True"
| "nullable (NTIMES r n) = (if n = 0 then True else nullable r)"

fun
 der :: "char \<Rightarrow> rexp \<Rightarrow> rexp"
where
  "der c (ZERO) = ZERO"
| "der c (ONE) = ZERO"
| "der c (CH d) = (if c = d then ONE else ZERO)"
| "der c (ALT r1 r2) = ALT (der c r1) (der c r2)"
| "der c (SEQ r1 r2) = 
     (if nullable r1
      then ALT (SEQ (der c r1) r2) (der c r2)
      else SEQ (der c r1) r2)"
| "der c (STAR r) = SEQ (der c r) (STAR r)"
| "der c (NTIMES r n) = (if n = 0 then ZERO else SEQ (der c r) (NTIMES r (n - 1)))"


fun 
 ders :: "string \<Rightarrow> rexp \<Rightarrow> rexp"
where
  "ders [] r = r"
| "ders (c # s) r = ders s (der c r)"


lemma pow_empty_iff:
  shows "[] \<in> (L r) ^^ n \<longleftrightarrow> (if n = 0 then True else [] \<in> (L r))"
  by (induct n) (auto simp add: Sequ_def)

lemma nullable_correctness:
  shows "nullable r  \<longleftrightarrow> [] \<in> (L r)"
  by (induct r) (auto simp add: Sequ_def pow_empty_iff) 

lemma der_correctness:
  shows "L (der c r) = Der c (L r)"
  apply (induct r) 
        apply(auto simp add: nullable_correctness Sequ_def)
  using Der_def apply force
  using Der_def apply auto[1]
  apply (smt (verit, ccfv_SIG) Der_def append_eq_Cons_conv mem_Collect_eq)
  using Der_def apply force
  using Der_Sequ Sequ_def by auto

lemma ders_correctness:
  shows "L (ders s r) = Ders s (L r)"
  by (induct s arbitrary: r)
     (simp_all add: Ders_def der_correctness Der_def)

lemma ders_append:
  shows "ders (s1 @ s2) r = ders s2 (ders s1 r)"
  by (induct s1 arbitrary: s2 r) (auto)

lemma ders_snoc:
  shows "ders (s @ [c]) r = der c (ders s r)"
  by (simp add: ders_append)


end