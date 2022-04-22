theory GeneralRegexBound imports 
"BasicIdentities" 
begin


lemma non_zero_size:
  shows "rsize r \<ge> Suc 0"
  apply(induct r)
  apply auto done

corollary size_geq1:
  shows "rsize r \<ge> 1"
  by (simp add: non_zero_size)


definition SEQ_set where
  "SEQ_set A n \<equiv> {RSEQ r1 r2 | r1 r2. r1 \<in> A \<and> r2 \<in> A \<and> rsize r1 + rsize r2 \<le> n}"

definition SEQ_set_cartesian where
"SEQ_set_cartesian A  = {RSEQ r1 r2 | r1 r2. r1 \<in> A \<and> r2 \<in> A}"

definition ALT_set where
"ALT_set A n \<equiv> {RALTS rs | rs. set rs \<subseteq> A \<and> sum_list (map rsize rs) \<le> n}"

definition ALTs_set
  where
  "ALTs_set A n \<equiv> {RALTS rs | rs. \<forall>r \<in> set rs. r \<in> A \<and> sum_list (map rsize rs) \<le> n}"



definition
  "sizeNregex N \<equiv> {r. rsize r \<le> N}"



lemma sizenregex_induct1:
  "sizeNregex (Suc n) = (({RZERO, RONE} \<union> {RCHAR c| c. True}) 
                       \<union> (RSTAR ` sizeNregex n) \<union>
                         (SEQ_set (sizeNregex n) n)
                       \<union>  (ALTs_set (sizeNregex n) n))"
  apply(auto)
        apply(case_tac x)
             apply(auto simp add: SEQ_set_def)
  using sizeNregex_def apply force
  using sizeNregex_def apply auto[1]
  apply (simp add: sizeNregex_def)
         apply (simp add: sizeNregex_def)
         apply (simp add: ALTs_set_def)
  apply (metis imageI list.set_map member_le_sum_list order_trans)
  apply (simp add: sizeNregex_def)
  apply (simp add: sizeNregex_def)
  apply (simp add: sizeNregex_def)
  using sizeNregex_def apply force
  apply (simp add: sizeNregex_def)
  apply (simp add: sizeNregex_def)
  apply (simp add: ALTs_set_def)
  apply(simp add: sizeNregex_def)
  apply(auto)
  using ex_in_conv by fastforce

lemma sizeN_inclusion:
  shows "sizeNregex n   \<subseteq> sizeNregex (Suc n)"
  by (simp add: Collect_mono sizeNregex_def)

lemma s4:
  "SEQ_set A n \<subseteq> SEQ_set_cartesian A"
  using SEQ_set_cartesian_def SEQ_set_def by fastforce

lemma s5:
  "finite A \<Longrightarrow> finite (SEQ_set_cartesian A)"
  apply(subgoal_tac "SEQ_set_cartesian A = (\<lambda>(x1, x2). RSEQ x1 x2) ` (A \<times> A)")
  apply simp
  unfolding SEQ_set_cartesian_def
  apply(auto)
  done

thm size_list_def

definition ALTs_set_length
  where
  "ALTs_set_length A n l \<equiv> {RALTS rs | rs. \<forall>r \<in> set rs. r \<in> A 
                                      \<and> sum_list (map rsize rs) \<le> n 
                                      \<and> length rs \<le> l}"


definition ALTs_set_length2
  where
  "ALTs_set_length2 A l \<equiv> {RALTS rs | rs. \<forall>r \<in> set rs. r \<in> A \<and> length rs \<le> l}"

definition set_length2
  where
  "set_length2 A l \<equiv> {rs. \<forall>r \<in> set rs. r \<in> A \<and> length rs \<le> l}"


lemma r000: 
  shows "ALTs_set_length A n l \<subseteq> ALTs_set_length2 A l"
  apply(auto simp add: ALTs_set_length2_def ALTs_set_length_def)
  done


lemma r02: 
  shows "set_length2 A 0 \<subseteq> {[]}"
  apply(auto simp add: set_length2_def)
  apply(case_tac x)
  apply(auto)
  done

lemma r03:
  shows "set_length2 A (Suc n) \<subseteq> 
          {[]} \<union> (\<lambda>(h, t). h # t) ` (A \<times> (set_length2 A n))"
  apply(auto simp add: set_length2_def)
  apply(case_tac x)
   apply(auto)
  done

lemma r1:
  assumes "finite A" 
  shows "finite (set_length2 A n)"
  using assms
  apply(induct n)
  apply(rule finite_subset)
    apply(rule r02)
   apply(simp)    
  apply(rule finite_subset)
   apply(rule r03)
  apply(simp)
  done

lemma size_sum_more_than_len:
  shows "sum_list (map rsize rs) \<ge> length rs"
  apply(induct rs)
   apply simp
  apply simp
  apply(subgoal_tac "rsize a \<ge> 1")
   apply linarith
  using size_geq1 by auto


lemma sum_list_len:
  shows " sum_list (map rsize rs) \<le> n \<Longrightarrow> length rs \<le> n"
  by (meson order.trans size_sum_more_than_len)

  


lemma t2:
  shows "ALTs_set A n \<subseteq> ALTs_set_length A n n"
  unfolding ALTs_set_length_def ALTs_set_def
  apply(auto)
  using sum_list_len by blast

  
thm ALTs_set_def

lemma s8_aux:
  assumes "finite A" 
  shows "finite (ALTs_set_length A n n)"
proof -
  have "finite A" by fact
  then have "finite (set_length2 A n)"
    by (simp add: r1)
  moreover have "(RALTS ` (set_length2 A n)) = ALTs_set_length2 A n"
    unfolding ALTs_set_length2_def set_length2_def
    by (auto)
  ultimately have "finite (ALTs_set_length2 A n)"
    by (metis finite_imageI)
  then show ?thesis
    by (metis infinite_super r000)
qed


lemma char_finite:
  shows "finite  {RCHAR c |c. True}"
  apply simp
  apply(subgoal_tac "finite (RCHAR ` (UNIV::char set))")
   prefer 2
   apply simp
  by (simp add: full_SetCompr_eq)


lemma finite_size_n:
  shows
  "finite (sizeNregex n)"
  apply(induct n)
   apply(simp add: sizeNregex_def)
  apply (metis (mono_tags, lifting) not_finite_existsD not_one_le_zero size_geq1)
  apply(subst sizenregex_induct1)
  apply(simp only: finite_Un)
  apply(rule conjI)+
      apply(simp)
  using char_finite apply blast
    apply(simp)
   apply(rule finite_subset)
    apply(rule s4)
   apply(rule s5)
   apply(simp)
  apply(rule finite_subset)
   apply(rule t2)
  apply(rule s8_aux)
  apply(simp)
  done

lemma three_easy_cases0: shows 
"rsize (rders_simp RZERO s) \<le> Suc 0"
  apply(induct s)
   apply simp
  apply simp
  done


lemma three_easy_cases1: shows 
"rsize (rders_simp RONE s) \<le> Suc 0"
    apply(induct s)
   apply simp
  apply simp
  using three_easy_cases0 by auto


lemma three_easy_casesC: shows
"rsize (rders_simp (RCHAR c) s) \<le> Suc 0"
  apply(induct s)
   apply simp
  apply simp
  apply(case_tac " a = c")
  using three_easy_cases1 apply blast
  apply simp
  using three_easy_cases0 by force
  

unused_thms


end

