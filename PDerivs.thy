   
theory PDerivs
  imports PosixSpec 
begin



abbreviation
  "SEQs rs r \<equiv> (\<Union>r' \<in> rs. {SEQ r' r})"

lemma SEQs_eq_image:
  "SEQs rs r = (\<lambda>r'. SEQ r' r) ` rs"
  by auto

fun
  pder :: "char \<Rightarrow> rexp \<Rightarrow> rexp set"
where
  "pder c ZERO = {}"
| "pder c ONE = {}"
| "pder c (CH d) = (if c = d then {ONE} else {})"
| "pder c (ALT r1 r2) = (pder c r1) \<union> (pder c r2)"
| "pder c (SEQ r1 r2) = 
    (if nullable r1 then SEQs (pder c r1) r2 \<union> pder c r2 else SEQs (pder c r1) r2)"
| "pder c (STAR r) = SEQs (pder c r) (STAR r)"

fun
  pders :: "char list \<Rightarrow> rexp \<Rightarrow> rexp set"
where
  "pders [] r = {r}"
| "pders (c # s) r = \<Union> (pders s ` pder c r)"

abbreviation
 pder_set :: "char \<Rightarrow> rexp set \<Rightarrow> rexp set"
where
  "pder_set c rs \<equiv> \<Union> (pder c ` rs)"

abbreviation
  pders_set :: "char list \<Rightarrow> rexp set \<Rightarrow> rexp set"
where
  "pders_set s rs \<equiv> \<Union> (pders s ` rs)"

lemma pders_append:
  "pders (s1 @ s2) r = \<Union> (pders s2 ` pders s1 r)"
by (induct s1 arbitrary: r) (simp_all)

lemma pders_snoc:
  shows "pders (s @ [c]) r = pder_set c (pders s r)"
by (simp add: pders_append)

lemma pders_simps [simp]:
  shows "pders s ZERO = (if s = [] then {ZERO} else {})"
  and   "pders s ONE = (if s = [] then {ONE} else {})"
  and   "pders s (ALT r1 r2) = (if s = [] then {ALT r1 r2} else (pders s r1) \<union> (pders s r2))"
by (induct s) (simp_all)

lemma pders_CHAR:
  shows "pders s (CH c) \<subseteq> {CH c, ONE}"
by (induct s) (simp_all)

subsection \<open>Relating left-quotients and partial derivatives\<close>

lemma Sequ_UNION_distrib:
shows "A ;; \<Union>(M ` I) = \<Union>((\<lambda>i. A ;; M i) ` I)"
and   "\<Union>(M ` I) ;; A = \<Union>((\<lambda>i. M i ;; A) ` I)"
by (auto simp add: Sequ_def)


lemma Der_pder:
  shows "Der c (L r) = \<Union> (L ` pder c r)"
by (induct r) (simp_all add: nullable_correctness Sequ_UNION_distrib)
  
lemma Ders_pders:
  shows "Ders s (L r) = \<Union> (L ` pders s r)"
proof (induct s arbitrary: r)
  case (Cons c s)
  have ih: "\<And>r. Ders s (L r) = \<Union> (L ` pders s r)" by fact
  have "Ders (c # s) (L r) = Ders s (Der c (L r))" by (simp add: Ders_def Der_def)
  also have "\<dots> = Ders s (\<Union> (L ` pder c r))" by (simp add: Der_pder)
  also have "\<dots> = (\<Union>A\<in>(L ` (pder c r)). (Ders s A))"
    by (auto simp add:  Ders_def)
  also have "\<dots> = \<Union> (L ` (pders_set s (pder c r)))"
    using ih by auto
  also have "\<dots> = \<Union> (L ` (pders (c # s) r))" by simp
  finally show "Ders (c # s) (L r) = \<Union> (L ` pders (c # s) r)" .
qed (simp add: Ders_def)

subsection \<open>Relating derivatives and partial derivatives\<close>

lemma der_pder:
  shows "\<Union> (L ` (pder c r)) = L (der c r)"
unfolding der_correctness Der_pder by simp

lemma ders_pders:
  shows "\<Union> (L ` (pders s r)) = L (ders s r)"
unfolding der_correctness ders_correctness Ders_pders by simp


subsection \<open>Finiteness property of partial derivatives\<close>

definition
  pders_Set :: "string set \<Rightarrow> rexp \<Rightarrow> rexp set"
where
  "pders_Set A r \<equiv> \<Union>x \<in> A. pders x r"

lemma pders_Set_subsetI:
  assumes "\<And>s. s \<in> A \<Longrightarrow> pders s r \<subseteq> C"
  shows "pders_Set A r \<subseteq> C"
using assms unfolding pders_Set_def by (rule UN_least)

lemma pders_Set_union:
  shows "pders_Set (A \<union> B) r = (pders_Set A r \<union> pders_Set B r)"
by (simp add: pders_Set_def)

lemma pders_Set_subset:
  shows "A \<subseteq> B \<Longrightarrow> pders_Set A r \<subseteq> pders_Set B r"
by (auto simp add: pders_Set_def)

definition
  "UNIV1 \<equiv> UNIV - {[]}"

lemma pders_Set_ZERO [simp]:
  shows "pders_Set UNIV1 ZERO = {}"
unfolding UNIV1_def pders_Set_def by auto

lemma pders_Set_ONE [simp]:
  shows "pders_Set UNIV1 ONE = {}"
unfolding UNIV1_def pders_Set_def by (auto split: if_splits)

lemma pders_Set_CHAR [simp]:
  shows "pders_Set UNIV1 (CH c) = {ONE}"
unfolding UNIV1_def pders_Set_def
apply(auto)
apply(frule rev_subsetD)
apply(rule pders_CHAR)
apply(simp)
apply(case_tac xa)
apply(auto split: if_splits)
done

lemma pders_Set_ALT [simp]:
  shows "pders_Set UNIV1 (ALT r1 r2) = pders_Set UNIV1 r1 \<union> pders_Set UNIV1 r2"
unfolding UNIV1_def pders_Set_def by auto


text \<open>Non-empty suffixes of a string (needed for the cases of @{const SEQ} and @{const STAR} below)\<close>

definition
  "PSuf s \<equiv> {v. v \<noteq> [] \<and> (\<exists>u. u @ v = s)}"

lemma PSuf_snoc:
  shows "PSuf (s @ [c]) = (PSuf s) ;; {[c]} \<union> {[c]}"
unfolding PSuf_def Sequ_def
by (auto simp add: append_eq_append_conv2 append_eq_Cons_conv)

lemma PSuf_Union:
  shows "(\<Union>v \<in> PSuf s ;; {[c]}. f v) = (\<Union>v \<in> PSuf s. f (v @ [c]))"
by (auto simp add: Sequ_def)

lemma pders_Set_snoc:
  shows "pders_Set (PSuf s ;; {[c]}) r = (pder_set c (pders_Set (PSuf s) r))"
unfolding pders_Set_def
by (simp add: PSuf_Union pders_snoc)

lemma pders_SEQ:
  shows "pders s (SEQ r1 r2) \<subseteq> SEQs (pders s r1) r2 \<union> (pders_Set (PSuf s) r2)"
proof (induct s rule: rev_induct)
  case (snoc c s)
  have ih: "pders s (SEQ r1 r2) \<subseteq> SEQs (pders s r1) r2 \<union> (pders_Set (PSuf s) r2)" 
    by fact
  have "pders (s @ [c]) (SEQ r1 r2) = pder_set c (pders s (SEQ r1 r2))" 
    by (simp add: pders_snoc)
  also have "\<dots> \<subseteq> pder_set c (SEQs (pders s r1) r2 \<union> (pders_Set (PSuf s) r2))"
    using ih by fastforce
  also have "\<dots> = pder_set c (SEQs (pders s r1) r2) \<union> pder_set c (pders_Set (PSuf s) r2)"
    by (simp)
  also have "\<dots> = pder_set c (SEQs (pders s r1) r2) \<union> pders_Set (PSuf s ;; {[c]}) r2"
    by (simp add: pders_Set_snoc)
  also 
  have "\<dots> \<subseteq> pder_set c (SEQs (pders s r1) r2) \<union> pder c r2 \<union> pders_Set (PSuf s ;; {[c]}) r2"
    by auto
  also 
  have "\<dots> \<subseteq> SEQs (pder_set c (pders s r1)) r2 \<union> pder c r2 \<union> pders_Set (PSuf s ;; {[c]}) r2"
    by (auto simp add: if_splits)
  also have "\<dots> = SEQs (pders (s @ [c]) r1) r2 \<union> pder c r2 \<union> pders_Set (PSuf s ;; {[c]}) r2"
    by (simp add: pders_snoc)
  also have "\<dots> \<subseteq> SEQs (pders (s @ [c]) r1) r2 \<union> pders_Set (PSuf (s @ [c])) r2"
    unfolding pders_Set_def by (auto simp add: PSuf_snoc)  
  finally show ?case .
qed (simp) 

lemma pders_Set_SEQ_aux1:
  assumes a: "s \<in> UNIV1"
  shows "pders_Set (PSuf s) r \<subseteq> pders_Set UNIV1 r"
using a unfolding UNIV1_def PSuf_def pders_Set_def by auto

lemma pders_Set_SEQ_aux2:
  assumes a: "s \<in> UNIV1"
  shows "SEQs (pders s r1) r2 \<subseteq> SEQs (pders_Set UNIV1 r1) r2"
using a unfolding pders_Set_def by auto

lemma pders_Set_SEQ:
  shows "pders_Set UNIV1 (SEQ r1 r2) \<subseteq> SEQs (pders_Set UNIV1 r1) r2 \<union> pders_Set UNIV1 r2"
apply(rule pders_Set_subsetI)
apply(rule subset_trans)
apply(rule pders_SEQ)
using pders_Set_SEQ_aux1 pders_Set_SEQ_aux2
apply auto
apply blast
done

lemma pders_STAR:
  assumes a: "s \<noteq> []"
  shows "pders s (STAR r) \<subseteq> SEQs (pders_Set (PSuf s) r) (STAR r)"
using a
proof (induct s rule: rev_induct)
  case (snoc c s)
  have ih: "s \<noteq> [] \<Longrightarrow> pders s (STAR r) \<subseteq> SEQs (pders_Set (PSuf s) r) (STAR r)" by fact
  { assume asm: "s \<noteq> []"
    have "pders (s @ [c]) (STAR r) = pder_set c (pders s (STAR r))" by (simp add: pders_snoc)
    also have "\<dots> \<subseteq> pder_set c (SEQs (pders_Set (PSuf s) r) (STAR r))"
      using ih[OF asm] by fast
    also have "\<dots> \<subseteq> SEQs (pder_set c (pders_Set (PSuf s) r)) (STAR r) \<union> pder c (STAR r)"
      by (auto split: if_splits)
    also have "\<dots> \<subseteq> SEQs (pders_Set (PSuf (s @ [c])) r) (STAR r) \<union> (SEQs (pder c r) (STAR r))"
      by (simp only: PSuf_snoc pders_Set_snoc pders_Set_union)
         (auto simp add: pders_Set_def)
    also have "\<dots> = SEQs (pders_Set (PSuf (s @ [c])) r) (STAR r)"
      by (auto simp add: PSuf_snoc PSuf_Union pders_snoc pders_Set_def)
    finally have ?case .
  }
  moreover
  { assume asm: "s = []"
    then have ?case by (auto simp add: pders_Set_def pders_snoc PSuf_def)
  }
  ultimately show ?case by blast
qed (simp)

lemma pders_Set_STAR:
  shows "pders_Set UNIV1 (STAR r) \<subseteq> SEQs (pders_Set UNIV1 r) (STAR r)"
apply(rule pders_Set_subsetI)
apply(rule subset_trans)
apply(rule pders_STAR)
apply(simp add: UNIV1_def)
apply(simp add: UNIV1_def PSuf_def)
apply(auto simp add: pders_Set_def)
done

lemma finite_SEQs [simp]:
  assumes a: "finite A"
  shows "finite (SEQs A r)"
using a by auto


lemma finite_pders_Set_UNIV1:
  shows "finite (pders_Set UNIV1 r)"
apply(induct r)
apply(simp_all add: 
  finite_subset[OF pders_Set_SEQ]
  finite_subset[OF pders_Set_STAR])
done
    
lemma pders_Set_UNIV:
  shows "pders_Set UNIV r = pders [] r \<union> pders_Set UNIV1 r"
unfolding UNIV1_def pders_Set_def
by blast

lemma finite_pders_Set_UNIV:
  shows "finite (pders_Set UNIV r)"
unfolding pders_Set_UNIV
by (simp add: finite_pders_Set_UNIV1)

lemma finite_pders_set:
  shows "finite (pders_Set A r)"
by (metis finite_pders_Set_UNIV pders_Set_subset rev_finite_subset subset_UNIV)


text \<open>The following relationship between the alphabetic width of regular expressions
(called \<open>awidth\<close> below) and the number of partial derivatives was proved
by Antimirov~\cite{Antimirov95} and formalized by Max Haslbeck.\<close>

fun awidth :: "rexp \<Rightarrow> nat" where
"awidth ZERO = 0" |
"awidth ONE = 0" |
"awidth (CH a) = 1" |
"awidth (ALT r1 r2) = awidth r1 + awidth r2" |
"awidth (SEQ r1 r2) = awidth r1 + awidth r2" |
"awidth (STAR r1) = awidth r1"

lemma card_SEQs_pders_Set_le:
  shows  "card (SEQs (pders_Set A r) s) \<le> card (pders_Set A r)"
  using finite_pders_set 
  unfolding SEQs_eq_image 
  by (rule card_image_le)

lemma card_pders_set_UNIV1_le_awidth: 
  shows "card (pders_Set UNIV1 r) \<le> awidth r"
proof (induction r)
  case (ALT r1 r2)
  have "card (pders_Set UNIV1 (ALT r1 r2)) = card (pders_Set UNIV1 r1 \<union> pders_Set UNIV1 r2)" by simp
  also have "\<dots> \<le> card (pders_Set UNIV1 r1) + card (pders_Set UNIV1 r2)"
    by(simp add: card_Un_le)
  also have "\<dots> \<le> awidth (ALT r1 r2)" using ALT.IH by simp
  finally show ?case .
next
  case (SEQ r1 r2)
  have "card (pders_Set UNIV1 (SEQ r1 r2)) \<le> card (SEQs (pders_Set UNIV1 r1) r2 \<union> pders_Set UNIV1 r2)"
    by (simp add: card_mono finite_pders_set pders_Set_SEQ)
  also have "\<dots> \<le> card (SEQs (pders_Set UNIV1 r1) r2) + card (pders_Set UNIV1 r2)"
    by (simp add: card_Un_le)
  also have "\<dots> \<le> card (pders_Set UNIV1 r1) + card (pders_Set UNIV1 r2)"
    by (simp add: card_SEQs_pders_Set_le)
  also have "\<dots> \<le> awidth (SEQ r1 r2)" using SEQ.IH by simp
  finally show ?case .
next
  case (STAR r)
  have "card (pders_Set UNIV1 (STAR r)) \<le> card (SEQs (pders_Set UNIV1 r) (STAR r))"
    by (simp add: card_mono finite_pders_set pders_Set_STAR)
  also have "\<dots> \<le> card (pders_Set UNIV1 r)" by (rule card_SEQs_pders_Set_le)
  also have "\<dots> \<le> awidth (STAR r)" by (simp add: STAR.IH)
  finally show ?case .
qed (auto)

text\<open>Antimirov's Theorem 3.4:\<close>

theorem card_pders_set_UNIV_le_awidth: 
  shows "card (pders_Set UNIV r) \<le> awidth r + 1"
proof -
  have "card (insert r (pders_Set UNIV1 r)) \<le> Suc (card (pders_Set UNIV1 r))"
    by(auto simp: card_insert_if[OF finite_pders_Set_UNIV1])
  also have "\<dots> \<le> Suc (awidth r)" by(simp add: card_pders_set_UNIV1_le_awidth)
  finally show ?thesis by(simp add: pders_Set_UNIV)
qed 

text\<open>Antimirov's Corollary 3.5:\<close>
(*W stands for word set*)
corollary card_pders_set_le_awidth: 
  shows "card (pders_Set W r) \<le> awidth r + 1"
proof -
  have "card (pders_Set W r) \<le> card (pders_Set UNIV r)"
    by (simp add: card_mono finite_pders_set pders_Set_subset)
  also have "... \<le> awidth r + 1"
    by (rule card_pders_set_UNIV_le_awidth)
  finally show "card (pders_Set W r) \<le> awidth r + 1" by simp
qed

(* other result by antimirov *)

lemma card_pders_awidth: 
  shows "card (pders s r) \<le> awidth r + 1"
proof -
  have "pders s r \<subseteq> pders_Set UNIV r"
    using pders_Set_def by auto
  then have "card (pders s r) \<le> card (pders_Set UNIV r)"
    by (simp add: card_mono finite_pders_set)
  then show "card (pders s r) \<le> awidth r + 1"
    using card_pders_set_le_awidth order_trans by blast
qed
    
  
  


fun subs :: "rexp \<Rightarrow> rexp set" where
"subs ZERO = {ZERO}" |
"subs ONE = {ONE}" |
"subs (CH a) = {CH a, ONE}" |
"subs (ALT r1 r2) = (subs r1 \<union> subs r2 \<union> {ALT r1 r2})" |
"subs (SEQ r1 r2) = (subs r1 \<union> subs r2 \<union> {SEQ r1 r2} \<union>  SEQs (subs r1) r2)" |
"subs (STAR r1) = (subs r1 \<union> {STAR r1} \<union> SEQs (subs r1) (STAR r1))"

lemma subs_finite:
  shows "finite (subs r)"
  apply(induct r) 
  apply(simp_all)
  done



lemma pders_subs:
  shows "pders s r \<subseteq> subs r"
  apply(induct r arbitrary: s)
       apply(simp)
      apply(simp)
     apply(simp add: pders_CHAR)
(*  SEQ case *)
    apply(simp)
    apply(rule subset_trans)
     apply(rule pders_SEQ)
    defer
(* ALT case *)
    apply(simp)
    apply(rule impI)
    apply(rule conjI)
  apply blast
    apply blast
(* STAR case *)
    apply(case_tac s)
    apply(simp)
   apply(rule subset_trans)
  thm pders_STAR
     apply(rule pders_STAR)
     apply(simp)
    apply(auto simp add: pders_Set_def)[1]
  apply(simp)
  apply(rule conjI)
   apply blast
apply(auto simp add: pders_Set_def)[1]
  done

fun size2 :: "rexp \<Rightarrow> nat" where
  "size2 ZERO = 1" |
  "size2 ONE = 1" |
  "size2 (CH c) = 1" |
  "size2 (ALT r1 r2) = Suc (size2 r1 + size2 r2)" |
  "size2 (SEQ r1 r2) = Suc (size2 r1 + size2 r2)" |
  "size2 (STAR r1) = Suc (size2 r1)" 


lemma size_rexp:
  fixes r :: rexp
  shows "1 \<le> size2 r"
  apply(induct r)
  apply(simp)
  apply(simp_all)
  done

lemma subs_size2:
  shows "\<forall>r1 \<in> subs r. size2 r1 \<le> Suc (size2 r * size2 r)"
  apply(induct r)
       apply(simp)
      apply(simp)
     apply(simp)
(* SEQ case *)
    apply(simp)
    apply(auto)[1]
  apply (smt Suc_n_not_le_n add.commute distrib_left le_Suc_eq left_add_mult_distrib nat_le_linear trans_le_add1)
  apply (smt Suc_le_mono Suc_n_not_le_n le_trans nat_le_linear power2_eq_square power2_sum semiring_normalization_rules(23) trans_le_add2)
  apply (smt Groups.add_ac(3) Suc_n_not_le_n distrib_left le_Suc_eq left_add_mult_distrib nat_le_linear trans_le_add1)
(*  ALT case  *)
   apply(simp)
   apply(auto)[1]
  apply (smt Groups.add_ac(2) Suc_le_mono Suc_n_not_le_n le_add2 linear order_trans power2_eq_square power2_sum)
  apply (smt Groups.add_ac(2) Suc_le_mono Suc_n_not_le_n left_add_mult_distrib linear mult.commute order.trans trans_le_add1)
(* STAR case *)
  apply(auto)[1]
  apply(drule_tac x="r'" in bspec)
   apply(simp)
  apply(rule le_trans)
   apply(assumption)
  apply(simp)
  using size_rexp
  apply(simp)
  done

lemma awidth_size:
  shows "awidth r \<le> size2 r"
  apply(induct r)
       apply(simp_all)
  done

lemma Sum1:
  fixes A B :: "nat set"
  assumes "A \<subseteq> B" "finite A" "finite B"
  shows "\<Sum>A \<le> \<Sum>B"
  using  assms
  by (simp add: sum_mono2)

lemma Sum2:
  fixes A :: "rexp set"  
  and   f g :: "rexp \<Rightarrow> nat" 
  assumes "finite A" "\<forall>x \<in> A. f x \<le> g x"
  shows "sum f A \<le> sum g A"
  using  assms
  apply(induct A)
   apply(auto)
  done





lemma pders_max_size:
  shows "(sum size2 (pders s r)) \<le> (Suc (size2 r)) ^ 3"
proof -
  have "(sum size2 (pders s r)) \<le> sum (\<lambda>_. Suc (size2 r  * size2 r)) (pders s r)" 
    apply(rule_tac Sum2)
     apply (meson pders_subs rev_finite_subset subs_finite)
    using pders_subs subs_size2 by blast
  also have "... \<le> (Suc (size2 r  * size2 r)) * (sum (\<lambda>_. 1) (pders s r))"
    by simp
  also have "... \<le> (Suc (size2 r  * size2 r)) * card (pders s r)"
    by simp
  also have "... \<le> (Suc (size2 r  * size2 r)) * (Suc (awidth r))"
    using Suc_eq_plus1 card_pders_awidth mult_le_mono2 by presburger
  also have "... \<le> (Suc (size2 r  * size2 r)) * (Suc (size2 r))"
    using Suc_le_mono awidth_size mult_le_mono2 by presburger
  also have "... \<le> (Suc (size2 r)) ^ 3"
    by (smt One_nat_def Suc_1 Suc_mult_le_cancel1 Suc_n_not_le_n antisym_conv le_Suc_eq mult.commute nat_le_linear numeral_3_eq_3 power2_eq_square power2_le_imp_le power_Suc size_rexp)    
  finally show ?thesis  .
qed
  
lemma pders_Set_max_size:
  shows "(sum size2 (pders_Set A r)) \<le> (Suc (size2 r)) ^ 3"
proof -
  have "(sum size2 (pders_Set A r)) \<le> sum (\<lambda>_. Suc (size2 r  * size2 r)) (pders_Set A r)" 
    apply(rule_tac Sum2)
     apply (simp add: finite_pders_set)
    by (meson pders_Set_subsetI pders_subs subs_size2 subsetD)
  also have "... \<le> (Suc (size2 r  * size2 r)) * (sum (\<lambda>_. 1) (pders_Set A r))"
    by simp
  also have "... \<le> (Suc (size2 r  * size2 r)) * card (pders_Set A r)"
    by simp
  also have "... \<le> (Suc (size2 r  * size2 r)) * (Suc (awidth r))"
    using Suc_eq_plus1 card_pders_set_le_awidth mult_le_mono2 by presburger
  also have "... \<le> (Suc (size2 r  * size2 r)) * (Suc (size2 r))"
    using Suc_le_mono awidth_size mult_le_mono2 by presburger
  also have "... \<le> (Suc (size2 r)) ^ 3"
    by (smt One_nat_def Suc_1 Suc_mult_le_cancel1 Suc_n_not_le_n antisym_conv le_Suc_eq mult.commute nat_le_linear numeral_3_eq_3 power2_eq_square power2_le_imp_le power_Suc size_rexp)    
  finally show ?thesis  .
qed    

fun height :: "rexp \<Rightarrow> nat" where
  "height ZERO = 1" |
  "height ONE = 1" |
  "height (CH c) = 1" |
  "height (ALT r1 r2) = Suc (max (height r1) (height r2))" |
  "height (SEQ r1 r2) = Suc (max (height r1) (height r2))" |
  "height (STAR r1) = Suc (height r1)" 

lemma height_size2:
  shows "height r \<le> size2 r"
  apply(induct r)
  apply(simp_all)
  done

lemma height_rexp:
  fixes r :: rexp
  shows "1 \<le> height r"
  apply(induct r)
  apply(simp_all)
  done

lemma subs_height:
  shows "\<forall>r1 \<in> subs r. height r1 \<le> Suc (height r)"
  apply(induct r)
  apply(auto)+
  done  

fun lin_concat :: "(char \<times> rexp) \<Rightarrow> rexp \<Rightarrow> (char \<times> rexp)" (infixl "[.]" 91)
  where
"(c, ZERO) [.] t = (c, ZERO)"
| "(c, ONE) [.] t = (c, t)"
| "(c, p) [.] t = (c, SEQ p t)"


fun circle_concat :: "(char \<times> rexp ) set \<Rightarrow> rexp \<Rightarrow> (char \<times> rexp) set" ( infixl "\<circle>" 90)
  where
"l \<circle> ZERO = {}"
| "l \<circle> ONE = l"
| "l \<circle> t  = ( (\<lambda>p.  p [.] t) ` l ) "



fun linear_form :: "rexp \<Rightarrow>( char \<times> rexp ) set" 
  where
  "linear_form ZERO = {}"
| "linear_form ONE = {}"
| "linear_form (CH c)  = {(c, ONE)}"
| "linear_form (ALT r1 r2) = (linear_form) r1 \<union> (linear_form r2)"
| "linear_form (SEQ r1 r2) = (if (nullable r1) then (linear_form r1) \<circle> r2 \<union> linear_form r2 else  (linear_form r1) \<circle> r2) "
| "linear_form (STAR r ) = (linear_form r) \<circle> (STAR r)"


value "linear_form (SEQ (STAR (CH x)) (STAR (ALT (SEQ (CH x) (CH x)) (CH y)  ))  )"


value "linear_form  (STAR (ALT (SEQ (CH x) (CH x)) (CH y)  ))  "

fun pdero :: "char \<Rightarrow> rexp \<Rightarrow> rexp set"
  where
"pdero c t  = \<Union> ((\<lambda>(d, p). if d = c then {p} else {}) ` (linear_form t) )"

fun pderso :: "char list \<Rightarrow> rexp \<Rightarrow> rexp set"
  where
  "pderso [] r = {r}"
|  "pderso (c # s) r = \<Union> ( pderso s ` (pdero c r) )"

lemma pdero_result: 
  shows "pdero  c (STAR (ALT (CH c) (SEQ (CH c) (CH c)))) =  {SEQ (CH c)(STAR (ALT (CH c) (SEQ (CH c) (CH c)))),(STAR (ALT (CH c) (SEQ (CH c) (CH c))))}"
  apply(simp)
  by auto

fun concatLen :: "rexp \<Rightarrow> nat" where
"concatLen ZERO = 0" |
"concatLen ONE = 0" |
"concatLen (CH c) = 0" |
"concatLen (SEQ v1 v2) = Suc (max (concatLen v1) (concatLen v2))" |
" concatLen (ALT v1 v2) =  max (concatLen v1) (concatLen v2)" |
" concatLen (STAR v) = Suc (concatLen v)" 



end