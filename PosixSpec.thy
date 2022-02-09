   
theory PosixSpec
  imports RegLangs
begin

section \<open>"Plain" Values\<close>

datatype val = 
  Void
| Char char
| Seq val val
| Right val
| Left val
| Stars "val list"


section \<open>The string behind a value\<close>

fun 
  flat :: "val \<Rightarrow> string"
where
  "flat (Void) = []"
| "flat (Char c) = [c]"
| "flat (Left v) = flat v"
| "flat (Right v) = flat v"
| "flat (Seq v1 v2) = (flat v1) @ (flat v2)"
| "flat (Stars []) = []"
| "flat (Stars (v#vs)) = (flat v) @ (flat (Stars vs))" 

abbreviation
  "flats vs \<equiv> concat (map flat vs)"

lemma flat_Stars [simp]:
 "flat (Stars vs) = flats vs"
by (induct vs) (auto)


section \<open>Lexical Values\<close>

inductive 
  Prf :: "val \<Rightarrow> rexp \<Rightarrow> bool" ("\<Turnstile> _ : _" [100, 100] 100)
where
 "\<lbrakk>\<Turnstile> v1 : r1; \<Turnstile> v2 : r2\<rbrakk> \<Longrightarrow> \<Turnstile>  Seq v1 v2 : SEQ r1 r2"
| "\<Turnstile> v1 : r1 \<Longrightarrow> \<Turnstile> Left v1 : ALT r1 r2"
| "\<Turnstile> v2 : r2 \<Longrightarrow> \<Turnstile> Right v2 : ALT r1 r2"
| "\<Turnstile> Void : ONE"
| "\<Turnstile> Char c : CH c"
| "\<forall>v \<in> set vs. \<Turnstile> v : r \<and> flat v \<noteq> [] \<Longrightarrow> \<Turnstile> Stars vs : STAR r"

inductive_cases Prf_elims:
  "\<Turnstile> v : ZERO"
  "\<Turnstile> v : SEQ r1 r2"
  "\<Turnstile> v : ALT r1 r2"
  "\<Turnstile> v : ONE"
  "\<Turnstile> v : CH c"
  "\<Turnstile> vs : STAR r"

lemma Prf_Stars_appendE:
  assumes "\<Turnstile> Stars (vs1 @ vs2) : STAR r"
  shows "\<Turnstile> Stars vs1 : STAR r \<and> \<Turnstile> Stars vs2 : STAR r" 
using assms
by (auto intro: Prf.intros elim!: Prf_elims)


lemma flats_Prf_value:
  assumes "\<forall>s\<in>set ss. \<exists>v. s = flat v \<and> \<Turnstile> v : r"
  shows "\<exists>vs. flats vs = concat ss \<and> (\<forall>v\<in>set vs. \<Turnstile> v : r \<and> flat v \<noteq> [])"
using assms
apply(induct ss)
apply(auto)
apply(rule_tac x="[]" in exI)
apply(simp)
apply(case_tac "flat v = []")
apply(rule_tac x="vs" in exI)
apply(simp)
apply(rule_tac x="v#vs" in exI)
apply(simp)
done


lemma L_flat_Prf1:
  assumes "\<Turnstile> v : r" 
  shows "flat v \<in> L r"
using assms
by (induct) (auto simp add: Sequ_def Star_concat)

lemma L_flat_Prf2:
  assumes "s \<in> L r" 
  shows "\<exists>v. \<Turnstile> v : r \<and> flat v = s"
using assms
proof(induct r arbitrary: s)
  case (STAR r s)
  have IH: "\<And>s. s \<in> L r \<Longrightarrow> \<exists>v. \<Turnstile> v : r \<and> flat v = s" by fact
  have "s \<in> L (STAR r)" by fact
  then obtain ss where "concat ss = s" "\<forall>s \<in> set ss. s \<in> L r \<and> s \<noteq> []"
  using Star_split by auto  
  then obtain vs where "flats vs = s" "\<forall>v\<in>set vs. \<Turnstile> v : r \<and> flat v \<noteq> []"
  using IH flats_Prf_value by metis 
  then show "\<exists>v. \<Turnstile> v : STAR r \<and> flat v = s"
  using Prf.intros(6) flat_Stars by blast
next 
  case (SEQ r1 r2 s)
  then show "\<exists>v. \<Turnstile> v : SEQ r1 r2 \<and> flat v = s"
  unfolding Sequ_def L.simps by (fastforce intro: Prf.intros)
next
  case (ALT r1 r2 s)
  then show "\<exists>v. \<Turnstile> v : ALT r1 r2 \<and> flat v = s"
  unfolding L.simps by (fastforce intro: Prf.intros)
qed (auto intro: Prf.intros)


lemma L_flat_Prf:
  shows "L(r) = {flat v | v. \<Turnstile> v : r}"
using L_flat_Prf1 L_flat_Prf2 by blast



section \<open>Sets of Lexical Values\<close>

text \<open>
  Shows that lexical values are finite for a given regex and string.
\<close>

definition
  LV :: "rexp \<Rightarrow> string \<Rightarrow> val set"
where  "LV r s \<equiv> {v. \<Turnstile> v : r \<and> flat v = s}"

lemma LV_simps:
  shows "LV ZERO s = {}"
  and   "LV ONE s = (if s = [] then {Void} else {})"
  and   "LV (CH c) s = (if s = [c] then {Char c} else {})"
  and   "LV (ALT r1 r2) s = Left ` LV r1 s \<union> Right ` LV r2 s"
unfolding LV_def
by (auto intro: Prf.intros elim: Prf.cases)


abbreviation
  "Prefixes s \<equiv> {s'. prefix s' s}"

abbreviation
  "Suffixes s \<equiv> {s'. suffix s' s}"

abbreviation
  "SSuffixes s \<equiv> {s'. strict_suffix s' s}"

lemma Suffixes_cons [simp]:
  shows "Suffixes (c # s) = Suffixes s \<union> {c # s}"
by (auto simp add: suffix_def Cons_eq_append_conv)


lemma finite_Suffixes: 
  shows "finite (Suffixes s)"
by (induct s) (simp_all)

lemma finite_SSuffixes: 
  shows "finite (SSuffixes s)"
proof -
  have "SSuffixes s \<subseteq> Suffixes s"
   unfolding strict_suffix_def suffix_def by auto
  then show "finite (SSuffixes s)"
   using finite_Suffixes finite_subset by blast
qed

lemma finite_Prefixes: 
  shows "finite (Prefixes s)"
proof -
  have "finite (Suffixes (rev s))" 
    by (rule finite_Suffixes)
  then have "finite (rev ` Suffixes (rev s))" by simp
  moreover
  have "rev ` (Suffixes (rev s)) = Prefixes s"
  unfolding suffix_def prefix_def image_def
   by (auto)(metis rev_append rev_rev_ident)+
  ultimately show "finite (Prefixes s)" by simp
qed

lemma LV_STAR_finite:
  assumes "\<forall>s. finite (LV r s)"
  shows "finite (LV (STAR r) s)"
proof(induct s rule: length_induct)
  fix s::"char list"
  assume "\<forall>s'. length s' < length s \<longrightarrow> finite (LV (STAR r) s')"
  then have IH: "\<forall>s' \<in> SSuffixes s. finite (LV (STAR r) s')"
    by (force simp add: strict_suffix_def suffix_def) 
  define f where "f \<equiv> \<lambda>(v, vs). Stars (v # vs)"
  define S1 where "S1 \<equiv> \<Union>s' \<in> Prefixes s. LV r s'"
  define S2 where "S2 \<equiv> \<Union>s2 \<in> SSuffixes s. Stars -` (LV (STAR r) s2)"
  have "finite S1" using assms
    unfolding S1_def by (simp_all add: finite_Prefixes)
  moreover 
  with IH have "finite S2" unfolding S2_def
    by (auto simp add: finite_SSuffixes inj_on_def finite_vimageI)
  ultimately 
  have "finite ({Stars []} \<union> f ` (S1 \<times> S2))" by simp
  moreover 
  have "LV (STAR r) s \<subseteq> {Stars []} \<union> f ` (S1 \<times> S2)" 
  unfolding S1_def S2_def f_def
  unfolding LV_def image_def prefix_def strict_suffix_def 
  apply(auto)
  apply(case_tac x)
  apply(auto elim: Prf_elims)
  apply(erule Prf_elims)
  apply(auto)
  apply(case_tac vs)
  apply(auto intro: Prf.intros)  
  apply(rule exI)
  apply(rule conjI)
  apply(rule_tac x="flat a" in exI)
  apply(rule conjI)
  apply(rule_tac x="flats list" in exI)
  apply(simp)
   apply(blast)
  apply(simp add: suffix_def)
  using Prf.intros(6) by blast  
  ultimately
  show "finite (LV (STAR r) s)" by (simp add: finite_subset)
qed  
    

lemma LV_finite:
  shows "finite (LV r s)"
proof(induct r arbitrary: s)
  case (ZERO s) 
  show "finite (LV ZERO s)" by (simp add: LV_simps)
next
  case (ONE s)
  show "finite (LV ONE s)" by (simp add: LV_simps)
next
  case (CH c s)
  show "finite (LV (CH c) s)" by (simp add: LV_simps)
next 
  case (ALT r1 r2 s)
  then show "finite (LV (ALT r1 r2) s)" by (simp add: LV_simps)
next 
  case (SEQ r1 r2 s)
  define f where "f \<equiv> \<lambda>(v1, v2). Seq v1 v2"
  define S1 where "S1 \<equiv> \<Union>s' \<in> Prefixes s. LV r1 s'"
  define S2 where "S2 \<equiv> \<Union>s' \<in> Suffixes s. LV r2 s'"
  have IHs: "\<And>s. finite (LV r1 s)" "\<And>s. finite (LV r2 s)" by fact+
  then have "finite S1" "finite S2" unfolding S1_def S2_def
    by (simp_all add: finite_Prefixes finite_Suffixes)
  moreover
  have "LV (SEQ r1 r2) s \<subseteq> f ` (S1 \<times> S2)"
    unfolding f_def S1_def S2_def 
    unfolding LV_def image_def prefix_def suffix_def
    apply (auto elim!: Prf_elims)
    by (metis (mono_tags, lifting) mem_Collect_eq)  
  ultimately 
  show "finite (LV (SEQ r1 r2) s)"
    by (simp add: finite_subset)
next
  case (STAR r s)
  then show "finite (LV (STAR r) s)" by (simp add: LV_STAR_finite)
qed



section \<open>Our inductive POSIX Definition\<close>

inductive 
  Posix :: "string \<Rightarrow> rexp \<Rightarrow> val \<Rightarrow> bool" ("_ \<in> _ \<rightarrow> _" [100, 100, 100] 100)
where
  Posix_ONE: "[] \<in> ONE \<rightarrow> Void"
| Posix_CH: "[c] \<in> (CH c) \<rightarrow> (Char c)"
| Posix_ALT1: "s \<in> r1 \<rightarrow> v \<Longrightarrow> s \<in> (ALT r1 r2) \<rightarrow> (Left v)"
| Posix_ALT2: "\<lbrakk>s \<in> r2 \<rightarrow> v; s \<notin> L(r1)\<rbrakk> \<Longrightarrow> s \<in> (ALT r1 r2) \<rightarrow> (Right v)"
| Posix_SEQ: "\<lbrakk>s1 \<in> r1 \<rightarrow> v1; s2 \<in> r2 \<rightarrow> v2;
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> L r1 \<and> s\<^sub>4 \<in> L r2)\<rbrakk> \<Longrightarrow> 
    (s1 @ s2) \<in> (SEQ r1 r2) \<rightarrow> (Seq v1 v2)"
| Posix_STAR1: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> STAR r \<rightarrow> Stars vs; flat v \<noteq> [];
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> L r \<and> s\<^sub>4 \<in> L (STAR r))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> STAR r \<rightarrow> Stars (v # vs)"
| Posix_STAR2: "[] \<in> STAR r \<rightarrow> Stars []"

inductive_cases Posix_elims:
  "s \<in> ZERO \<rightarrow> v"
  "s \<in> ONE \<rightarrow> v"
  "s \<in> CH c \<rightarrow> v"
  "s \<in> ALT r1 r2 \<rightarrow> v"
  "s \<in> SEQ r1 r2 \<rightarrow> v"
  "s \<in> STAR r \<rightarrow> v"

lemma Posix1:
  assumes "s \<in> r \<rightarrow> v"
  shows "s \<in> L r" "flat v = s"
using assms
  by(induct s r v rule: Posix.induct)
    (auto simp add: Sequ_def)

text \<open>
  For a give value and string, our Posix definition 
  determines a unique value.
\<close>

lemma Posix_determ:
  assumes "s \<in> r \<rightarrow> v1" "s \<in> r \<rightarrow> v2"
  shows "v1 = v2"
using assms
proof (induct s r v1 arbitrary: v2 rule: Posix.induct)
  case (Posix_ONE v2)
  have "[] \<in> ONE \<rightarrow> v2" by fact
  then show "Void = v2" by cases auto
next 
  case (Posix_CH c v2)
  have "[c] \<in> CH c \<rightarrow> v2" by fact
  then show "Char c = v2" by cases auto
next 
  case (Posix_ALT1 s r1 v r2 v2)
  have "s \<in> ALT r1 r2 \<rightarrow> v2" by fact
  moreover
  have "s \<in> r1 \<rightarrow> v" by fact
  then have "s \<in> L r1" by (simp add: Posix1)
  ultimately obtain v' where eq: "v2 = Left v'" "s \<in> r1 \<rightarrow> v'" by cases auto 
  moreover
  have IH: "\<And>v2. s \<in> r1 \<rightarrow> v2 \<Longrightarrow> v = v2" by fact
  ultimately have "v = v'" by simp
  then show "Left v = v2" using eq by simp
next 
  case (Posix_ALT2 s r2 v r1 v2)
  have "s \<in> ALT r1 r2 \<rightarrow> v2" by fact
  moreover
  have "s \<notin> L r1" by fact
  ultimately obtain v' where eq: "v2 = Right v'" "s \<in> r2 \<rightarrow> v'" 
    by cases (auto simp add: Posix1) 
  moreover
  have IH: "\<And>v2. s \<in> r2 \<rightarrow> v2 \<Longrightarrow> v = v2" by fact
  ultimately have "v = v'" by simp
  then show "Right v = v2" using eq by simp
next
  case (Posix_SEQ s1 r1 v1 s2 r2 v2 v')
  have "(s1 @ s2) \<in> SEQ r1 r2 \<rightarrow> v'" 
       "s1 \<in> r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L r1 \<and> s\<^sub>4 \<in> L r2)" by fact+
  then obtain v1' v2' where "v' = Seq v1' v2'" "s1 \<in> r1 \<rightarrow> v1'" "s2 \<in> r2 \<rightarrow> v2'"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
  using Posix1(1) by fastforce+
  moreover
  have IHs: "\<And>v1'. s1 \<in> r1 \<rightarrow> v1' \<Longrightarrow> v1 = v1'"
            "\<And>v2'. s2 \<in> r2 \<rightarrow> v2' \<Longrightarrow> v2 = v2'" by fact+
  ultimately show "Seq v1 v2 = v'" by simp
next
  case (Posix_STAR1 s1 r v s2 vs v2)
  have "(s1 @ s2) \<in> STAR r \<rightarrow> v2" 
       "s1 \<in> r \<rightarrow> v" "s2 \<in> STAR r \<rightarrow> Stars vs" "flat v \<noteq> []"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L r \<and> s\<^sub>4 \<in> L (STAR r))" by fact+
  then obtain v' vs' where "v2 = Stars (v' # vs')" "s1 \<in> r \<rightarrow> v'" "s2 \<in> (STAR r) \<rightarrow> (Stars vs')"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
  using Posix1(1) apply fastforce
  apply (metis Posix1(1) Posix_STAR1.hyps(6) append_Nil append_Nil2)
  using Posix1(2) by blast
  moreover
  have IHs: "\<And>v2. s1 \<in> r \<rightarrow> v2 \<Longrightarrow> v = v2"
            "\<And>v2. s2 \<in> STAR r \<rightarrow> v2 \<Longrightarrow> Stars vs = v2" by fact+
  ultimately show "Stars (v # vs) = v2" by auto
next
  case (Posix_STAR2 r v2)
  have "[] \<in> STAR r \<rightarrow> v2" by fact
  then show "Stars [] = v2" by cases (auto simp add: Posix1)
qed


text \<open>
  Our POSIX values are lexical values.
\<close>

lemma Posix_LV:
  assumes "s \<in> r \<rightarrow> v"
  shows "v \<in> LV r s"
  using assms unfolding LV_def
  apply(induct rule: Posix.induct)
  apply(auto simp add: intro!: Prf.intros elim!: Prf_elims)
  done

lemma Posix_Prf:
  assumes "s \<in> r \<rightarrow> v"
  shows "\<Turnstile> v : r"
  using assms Posix_LV LV_def
  by simp

end
