(**)
theory ClosedFormsBounds
  imports "GeneralRegexBound" "ClosedForms"
begin
lemma alts_ders_lambda_shape_ders:
  shows "\<forall>r \<in> set (map (\<lambda>r. rders_simp r ( s)) rs ). \<exists>r1 \<in> set rs. r = rders_simp r1 s"
  by (simp add: image_iff)

lemma rlist_bound:
  assumes "\<forall>r \<in> set rs. rsize r \<le> N"
  shows "sum_list (map rsize rs) \<le> N * (length rs)"
  using assms
  apply(induct rs)
  apply simp
  by simp

lemma alts_closed_form_bounded: 
  assumes "\<forall>r \<in> set rs. \<forall>s. rsize(rders_simp r s) \<le> N"
  shows "rsize (rders_simp (RALTS rs) s) \<le> max (Suc (N * (length rs))) (rsize (RALTS rs))"
  apply(induct s)
  apply simp
  apply(subst alts_closed_form_variant)
  apply force
  apply(subgoal_tac "rsize (rsimp (RALTS (map (\<lambda>r. rders_simp r (a # s)) rs))) \<le> rsize ( (RALTS (map (\<lambda>r. rders_simp r (a # s)) rs)))")
  prefer 2
  using rsimp_mono apply presburger
  apply(subgoal_tac "rsize (RALTS (map (\<lambda>r. rders_simp r (a # s)) rs)) =
                     Suc (sum_list  (map rsize (map (\<lambda>r. rders_simp r (a # s)) rs)))")
  prefer 2
  using rsize.simps(4) apply blast
  apply(subgoal_tac "sum_list (map rsize (map (\<lambda>r. rders_simp r (a # s)) rs )) \<le> N *  (length rs) ")
   apply linarith
  apply(subgoal_tac "\<forall>r \<in> set (map (\<lambda>r. rders_simp r (a # s)) rs ). rsize r \<le> N")
  prefer 2
  apply(subgoal_tac "\<forall>r \<in> set (map (\<lambda>r. rders_simp r (a # s)) rs ). \<exists>r1 \<in> set rs. r = rders_simp r1 (a # s)")
  prefer 2
  using alts_ders_lambda_shape_ders apply presburger
  using assms
  apply metis
  apply(frule rlist_bound)
  by fastforce


lemma alts_simp_ineq_unfold:
  shows "rsize (rsimp (RALTS rs)) \<le> Suc (sum_list (map rsize (rdistinct (rflts (map rsimp rs)) {})))"
  using rsimp_aalts_smaller by auto



inductive good :: "rrexp \<Rightarrow> bool"
  where
"RZERO \<notin> set rs \<Longrightarrow> good (RALTS rs)"
|"good RZERO"
|"good RONE"
|"good (RCHAR c)"
|"good (RSEQ r1 r2)"
|"good (RSTAR r0)"


lemma rdistinct_mono_list:
  shows " sum_list (map rsize (rdistinct (x5 @ rs) rset )) \<le>
        ( sum_list (map rsize x5)) + (sum_list (map rsize (rdistinct  rs ((set x5 ) \<union> rset))))"
  apply(induct x5 arbitrary: rs rset)
   apply simp
  apply(case_tac "a \<in> rset")
   apply simp
   apply (simp add: add.assoc insert_absorb trans_le_add2)
  apply simp
  by (metis Un_insert_right)


lemma flts_size_reduction_alts:
  shows " \<And>a rs noalts_set alts_set corr_set x5.
       \<lbrakk>\<And>noalts_set alts_set corr_set.
           (\<forall>r\<in>noalts_set. \<forall>xs. r \<noteq> RALTS xs) \<and>
           (\<forall>a\<in>alts_set. \<exists>xs. a = RALTS xs \<and> set xs \<subseteq> corr_set) \<Longrightarrow>
           Suc (sum_list (map rsize (rdistinct (rflts rs) (noalts_set \<union> corr_set))))
           \<le> Suc (sum_list (map rsize (rdistinct rs (insert RZERO (noalts_set \<union> alts_set)))));
        (\<forall>r\<in>noalts_set. \<forall>xs. r \<noteq> RALTS xs) \<and>
        (\<forall>a\<in>alts_set. \<exists>xs. a = RALTS xs \<and> set xs \<subseteq> corr_set);
        a = RALTS x5\<rbrakk>
       \<Longrightarrow> Suc (sum_list (map rsize (rdistinct (rflts (a # rs)) (noalts_set \<union> corr_set))))
           \<le> Suc (sum_list
                    (map rsize (rdistinct (a # rs) (insert RZERO (noalts_set \<union> alts_set)))))"
  apply(case_tac "a \<in> alts_set")
   apply simp
   apply(subgoal_tac "set x5 \<subseteq> corr_set")
  apply(subst rdistinct_concat)
  apply auto[1]
    apply presburger
   apply fastforce
  apply (subgoal_tac "a \<notin> noalts_set")
  prefer 2
  apply blast
  apply simp
  apply(subgoal_tac "sum_list (map rsize (rdistinct (x5 @ rflts rs) (noalts_set \<union> corr_set))) 
                   \<le> sum_list (map rsize x5 ) + sum_list (map rsize (rdistinct (rflts rs) ((set x5) \<union> (noalts_set \<union> corr_set))))")
  prefer 2
  using rdistinct_mono_list apply presburger
  apply(subgoal_tac "insert (RALTS x5) (noalts_set \<union> alts_set) = noalts_set \<union> (insert (RALTS x5) alts_set)")
   apply(simp only:)
  apply(subgoal_tac "sum_list (map rsize x5) + 
sum_list (map rsize (rdistinct (rflts rs) (noalts_set \<union> (corr_set \<union> (set x5))))) \<le>
Suc (sum_list (map rsize x5) +
                   sum_list
                    (map rsize
                      (rdistinct rs (insert RZERO (noalts_set \<union> insert (RALTS x5) alts_set)))))")
  
  apply (simp add: Un_left_commute inf_sup_aci(5))
   apply(subgoal_tac "sum_list (map rsize (rdistinct (rflts rs) (noalts_set \<union> (corr_set \<union> set x5))))
\<le> sum_list
                    (map rsize
                      (rdistinct rs (insert RZERO (noalts_set \<union> insert (RALTS x5) alts_set))))")
    apply linarith
   apply(subgoal_tac "\<forall>r \<in>  insert (RALTS x5) alts_set. \<exists>xs1.( r = RALTS xs1 \<and> set xs1 \<subseteq> corr_set \<union> set x5)")
    apply presburger
   apply (meson insert_iff sup.cobounded2 sup.coboundedI1)
  by blast




lemma flts_vs_nflts1:
  shows "(\<forall>r \<in> noalts_set. \<forall>xs. r \<noteq> RALTS xs)
 \<and> (\<forall>a \<in> alts_set. (\<exists>xs. a = RALTS xs \<and> set xs \<subseteq> corr_set))  
\<Longrightarrow>  (sum_list (map rsize (rdistinct ( rflts rs) (noalts_set \<union> corr_set)  )))
         \<le>  (sum_list (map rsize (rdistinct rs (insert RZERO (noalts_set \<union> alts_set) ))))"
    apply(induct rs arbitrary: noalts_set alts_set corr_set)
   apply simp
  apply(case_tac a)
       apply(case_tac "RZERO \<in> noalts_set")
        apply simp
       apply(subgoal_tac "RZERO \<notin> alts_set")
        apply simp
       apply fastforce
      apply(case_tac "RONE \<in> noalts_set")
       apply simp
      apply(subgoal_tac "RONE \<notin> alts_set")
  prefer 2
  apply fastforce
      apply(case_tac "RONE \<in> corr_set")
       apply(subgoal_tac "rflts (a # rs) = RONE # rflts rs")
        apply(simp only:)
        apply(subgoal_tac "rdistinct (RONE # rflts rs) (noalts_set \<union> corr_set) = 
                           rdistinct (rflts rs) (noalts_set \<union> corr_set)")
         apply(simp only:)
  apply(subgoal_tac "rdistinct (RONE # rs) (insert RZERO (noalts_set \<union> alts_set)) =
                     RONE # (rdistinct rs (insert RONE (insert RZERO (noalts_set \<union> alts_set)))) ")
          apply(simp only:)
  apply(subgoal_tac "rdistinct (rflts rs) (noalts_set \<union> corr_set) = 
                     rdistinct (rflts rs) (insert RONE (noalts_set \<union> corr_set))")
  apply (simp only:)
  apply(subgoal_tac "insert RONE (noalts_set \<union> corr_set) = (insert RONE noalts_set) \<union> corr_set")
            apply(simp only:)
  apply(subgoal_tac "insert RONE (insert RZERO (noalts_set \<union> alts_set)) = 
                     insert RZERO ((insert RONE noalts_set) \<union> alts_set)")
             apply(simp only:)
  apply(subgoal_tac "  (sum_list
                    (map rsize ( rdistinct rs (insert RZERO (insert RONE noalts_set \<union> alts_set)))))
                   \<le>  (sum_list
                    (map rsize (RONE # rdistinct rs (insert RZERO (insert RONE noalts_set \<union> alts_set)))))")
  apply (smt (verit, best) dual_order.trans insert_iff rrexp.distinct(15))
  apply (metis (no_types, opaque_lifting)  le_add_same_cancel2 list.simps(9) sum_list.Cons zero_le)
            apply fastforce
           apply fastforce
  apply (metis Un_iff insert_absorb)
         apply (metis UnE insertE insert_is_Un rdistinct.simps(2) rrexp.distinct(1))
        apply (meson UnCI rdistinct.simps(2))
  using rflts.simps(4) apply presburger
      apply simp
      apply(subgoal_tac "insert RONE (noalts_set \<union> corr_set) = (insert RONE noalts_set) \<union> corr_set")
  apply(simp only:)
  apply (metis Un_insert_left insertE rrexp.distinct(15))
      apply fastforce
     apply(case_tac "a \<in> noalts_set")
      apply simp
  apply(subgoal_tac "a \<notin> alts_set")
      prefer 2
      apply blast
  apply(case_tac "a \<in> corr_set")
      apply(subgoal_tac "noalts_set \<union> corr_set = insert a ( noalts_set  \<union> corr_set)")
  prefer 2
  apply fastforce
      apply(simp only:)
      apply(subgoal_tac "  sum_list
               (map rsize (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set))))
\<le>
                sum_list
               (map rsize (rdistinct (a # rs) (insert RZERO (noalts_set \<union> alts_set))))")

       apply(subgoal_tac 
"sum_list (map rsize (rdistinct (rflts (a # rs)) ((insert a noalts_set) \<union> corr_set)))
\<le>
 sum_list (map rsize (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set))))")
  apply fastforce
       apply simp
  apply(subgoal_tac "(insert a (noalts_set \<union> alts_set)) = (insert a noalts_set) \<union> alts_set")
        apply(simp only:)
        apply(subgoal_tac "noalts_set \<union> corr_set = (insert a noalts_set) \<union> corr_set")
  apply(simp only:)
  apply (metis insertE rrexp.distinct(21))
        apply blast
  
  apply fastforce
  apply force
     apply simp
     apply (metis Un_insert_left insert_iff rrexp.distinct(21))
    apply(case_tac "a \<in> noalts_set")
     apply simp
  apply(subgoal_tac "a \<notin> alts_set")
      prefer 2
      apply blast
  apply(case_tac "a \<in> corr_set")
      apply(subgoal_tac "noalts_set \<union> corr_set = insert a ( noalts_set  \<union> corr_set)")
  prefer 2
  apply fastforce
      apply(simp only:)
      apply(subgoal_tac "  sum_list
               (map rsize (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set))))
\<le>
                sum_list
               (map rsize (rdistinct (a # rs) (insert RZERO (noalts_set \<union> alts_set))))")

       apply(subgoal_tac 
"sum_list (map rsize (rdistinct (rflts (a # rs)) ((insert a noalts_set) \<union> corr_set)))
\<le>
 sum_list (map rsize (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set))))")
  apply fastforce
       apply simp
  apply(subgoal_tac "(insert a (noalts_set \<union> alts_set)) = (insert a noalts_set) \<union> alts_set")
        apply(simp only:)
        apply(subgoal_tac "noalts_set \<union> corr_set = (insert a noalts_set) \<union> corr_set")
  apply(simp only:)


  apply (metis insertE rrexp.distinct(25))
  apply blast
  apply fastforce
  apply force
     apply simp
  
    apply (metis Un_insert_left insertE rrexp.distinct(25))

  using Suc_le_mono flts_size_reduction_alts apply presburger
     apply(case_tac "a \<in> noalts_set")
      apply simp
  apply(subgoal_tac "a \<notin> alts_set")
      prefer 2
      apply blast
  apply(case_tac "a \<in> corr_set")
      apply(subgoal_tac "noalts_set \<union> corr_set = insert a ( noalts_set  \<union> corr_set)")
  prefer 2
  apply fastforce
      apply(simp only:)
      apply(subgoal_tac "  sum_list
               (map rsize (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set))))
\<le>
                sum_list
               (map rsize (rdistinct (a # rs) (insert RZERO (noalts_set \<union> alts_set))))")

       apply(subgoal_tac 
"sum_list (map rsize (rdistinct (rflts (a # rs)) ((insert a noalts_set) \<union> corr_set)))
\<le>
 sum_list (map rsize (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set))))")
  apply fastforce
       apply simp
  apply(subgoal_tac "(insert a (noalts_set \<union> alts_set)) = (insert a noalts_set) \<union> alts_set")
        apply(simp only:)
        apply(subgoal_tac "noalts_set \<union> corr_set = (insert a noalts_set) \<union> corr_set")
  apply(simp only:)
  apply (metis insertE rrexp.distinct(29))

        apply blast
  
  apply fastforce
  apply force
     apply simp
  apply (metis Un_insert_left insert_iff rrexp.distinct(29))
  done





lemma flts_vs_nflts:
  shows "(\<forall>r \<in> noalts_set. \<forall>xs. r \<noteq> RALTS xs)
 \<and> (\<forall>a \<in> alts_set. (\<exists>xs. a = RALTS xs \<and> set xs \<subseteq> corr_set))  
\<Longrightarrow> Suc (sum_list (map rsize (rdistinct ( rflts rs) (noalts_set \<union> corr_set)  )))
         \<le> Suc (sum_list (map rsize (rdistinct rs (insert RZERO (noalts_set \<union> alts_set) ))))"
  apply(induct rs arbitrary: noalts_set alts_set corr_set)
   apply simp
  apply(case_tac a)
       apply(case_tac "RZERO \<in> noalts_set")
        apply simp
       apply(subgoal_tac "RZERO \<notin> alts_set")
        apply simp
       apply fastforce
      apply(case_tac "RONE \<in> noalts_set")
       apply simp
      apply(subgoal_tac "RONE \<notin> alts_set")
  prefer 2
  apply fastforce
      apply(case_tac "RONE \<in> corr_set")
       apply(subgoal_tac "rflts (a # rs) = RONE # rflts rs")
        apply(simp only:)
        apply(subgoal_tac "rdistinct (RONE # rflts rs) (noalts_set \<union> corr_set) = 
                           rdistinct (rflts rs) (noalts_set \<union> corr_set)")
         apply(simp only:)
  apply(subgoal_tac "rdistinct (RONE # rs) (insert RZERO (noalts_set \<union> alts_set)) =
                     RONE # (rdistinct rs (insert RONE (insert RZERO (noalts_set \<union> alts_set)))) ")
          apply(simp only:)
  apply(subgoal_tac "rdistinct (rflts rs) (noalts_set \<union> corr_set) = 
                     rdistinct (rflts rs) (insert RONE (noalts_set \<union> corr_set))")
  apply (simp only:)
  apply(subgoal_tac "insert RONE (noalts_set \<union> corr_set) = (insert RONE noalts_set) \<union> corr_set")
            apply(simp only:)
  apply(subgoal_tac "insert RONE (insert RZERO (noalts_set \<union> alts_set)) = 
                     insert RZERO ((insert RONE noalts_set) \<union> alts_set)")
             apply(simp only:)
  apply(subgoal_tac " Suc (sum_list
                    (map rsize ( rdistinct rs (insert RZERO (insert RONE noalts_set \<union> alts_set)))))
                   \<le> Suc (sum_list
                    (map rsize (RONE # rdistinct rs (insert RZERO (insert RONE noalts_set \<union> alts_set)))))")
  apply (smt (verit, best) dual_order.trans insert_iff rrexp.distinct(15))
  apply (metis (no_types, opaque_lifting) add_Suc_right le_add_same_cancel2 list.simps(9) sum_list.Cons zero_le)
            apply fastforce
           apply fastforce
  apply (metis Un_iff insert_absorb)
         apply (metis UnE insertE insert_is_Un rdistinct.simps(2) rrexp.distinct(1))
        apply (meson UnCI rdistinct.simps(2))
  using rflts.simps(4) apply presburger
      apply simp
      apply(subgoal_tac "insert RONE (noalts_set \<union> corr_set) = (insert RONE noalts_set) \<union> corr_set")
  apply(simp only:)
  apply (metis Un_insert_left insertE rrexp.distinct(15))
      apply fastforce
     apply(case_tac "a \<in> noalts_set")
      apply simp
  apply(subgoal_tac "a \<notin> alts_set")
      prefer 2
      apply blast
  apply(case_tac "a \<in> corr_set")
      apply(subgoal_tac "noalts_set \<union> corr_set = insert a ( noalts_set  \<union> corr_set)")
  prefer 2
  apply fastforce
      apply(simp only:)
  apply (metis add_mono_thms_linordered_semiring(1) flts_vs_nflts1 le_numeral_extra(4) plus_1_eq_Suc)
  apply (metis add_mono_thms_linordered_semiring(1) flts_vs_nflts1 le_numeral_extra(4) plus_1_eq_Suc)
     apply(case_tac "a \<in> noalts_set")
      apply simp
  apply(subgoal_tac "a \<notin> alts_set")
      prefer 2
      apply blast
  apply(case_tac "a \<in> corr_set")
      apply(subgoal_tac "noalts_set \<union> corr_set = insert a ( noalts_set  \<union> corr_set)")
  prefer 2
  apply fastforce
      apply(simp only:)
  apply (metis add_mono_thms_linordered_semiring(1) flts_vs_nflts1 le_numeral_extra(4) plus_1_eq_Suc)
  apply (metis add_mono_thms_linordered_semiring(1) flts_vs_nflts1 le_numeral_extra(4) plus_1_eq_Suc)
   prefer 2
     apply(case_tac "a \<in> noalts_set")
      apply simp
  apply(subgoal_tac "a \<notin> alts_set")
      prefer 2
      apply blast
  apply(case_tac "a \<in> corr_set")
      apply(subgoal_tac "noalts_set \<union> corr_set = insert a ( noalts_set  \<union> corr_set)")
  prefer 2
  apply fastforce
      apply(simp only:)
  apply (metis add_mono_thms_linordered_semiring(1) flts_vs_nflts1 le_numeral_extra(4) plus_1_eq_Suc)
  apply (metis add_mono_thms_linordered_semiring(1) flts_vs_nflts1 le_numeral_extra(4) plus_1_eq_Suc)
  using flts_size_reduction_alts apply presburger
  done


lemma distinct_simp_ineq_general:
  shows "rsimp ` no_simp = has_simp \<and> finite no_simp \<Longrightarrow>Suc (sum_list (map rsize (rdistinct (map rsimp rs) has_simp)))
    \<le> Suc (sum_list (map rsize (rdistinct rs no_simp)))"
  apply(induct rs arbitrary: no_simp has_simp)
   apply simp
  apply(case_tac "a \<in> no_simp")
  apply(subgoal_tac "rsimp a \<in> has_simp")
    apply auto[1]
  apply blast
  apply(case_tac "rsimp a \<in> no_simp")
   apply(subgoal_tac "rsimp a \<in> has_simp")
  prefer 2
    apply (simp add: rev_image_eqI rsimp_idem)
  apply simp
   apply (metis finite_insert image_insert insert_absorb trans_le_add2)
  apply(case_tac "rsimp a \<notin> has_simp")
  apply simp
   apply (metis add_mono_thms_linordered_semiring(1) finite.insertI image_insert rsimp_mono)
  apply simp
  by (metis finite.insertI image_insert insert_absorb trans_le_add2)


lemma not_mentioned_elem_distinct_strong:
  shows "r \<noteq> a \<Longrightarrow> (r \<in> set (rdistinct rs rset)) = (r \<in> set (rdistinct rs (insert a rset)))"
  apply(induct rs arbitrary: rset)
   apply simp
  by force

lemma not_mentioned_elem_distinct:
  shows "r \<noteq> a \<Longrightarrow> (r \<in> set (rdistinct rs {})) = (r \<in> set (rdistinct rs (insert a {})))"
  by (metis not_mentioned_elem_distinct_strong)




lemma larger_acc_smaller_distinct_res0:
  assumes "ss \<subseteq> SS"
  shows "sum_list (map rsize (rdistinct rs SS)) \<le> sum_list (map rsize (rdistinct rs ss))"
  using assms
  apply(induct rs arbitrary: ss SS)
  apply simp
  apply(case_tac "a \<in> ss")
   apply(subgoal_tac "a \<in> SS")
    apply simp
   apply blast
  apply(case_tac "a \<in> SS")
   apply simp
   apply(subgoal_tac "insert a ss \<subseteq> SS")
    apply simp
  apply (simp add: trans_le_add2)
  apply blast
  apply(simp)
  apply(subgoal_tac "insert a ss \<subseteq> insert a SS")
   apply blast
  by blast


lemma without_flts_ineq:
  shows "Suc (sum_list (map rsize (rdistinct (rflts rs) {}) )) \<le> 
         Suc (sum_list (map rsize (rdistinct (    rs  ) {}  )))"
proof -
  have " Suc (sum_list (map rsize (rdistinct (rflts rs) {}) )) \<le>  
         Suc (sum_list (map rsize (rdistinct rs (insert RZERO {}))))"
    by (metis empty_iff flts_vs_nflts sup_bot_left)
  also have "... \<le>  Suc (sum_list (map rsize (rdistinct rs {})))" 
    by (simp add: larger_acc_smaller_distinct_res0)
  finally show ?thesis
    by blast
qed


lemma distinct_simp_ineq:
  shows "Suc (sum_list (map rsize (rdistinct (map rsimp rs) {})))
          \<le> Suc (sum_list (map rsize (rdistinct rs {})))"
  using distinct_simp_ineq_general by blast


lemma alts_simp_control:
  shows "rsize (rsimp (RALTS rs)) \<le> Suc (sum_list (map rsize (rdistinct rs {})))"
proof -
  have "rsize (rsimp (RALTS rs)) \<le> Suc (sum_list (map rsize (rdistinct (rflts (map rsimp rs)) {})))"
     using alts_simp_ineq_unfold by auto
   moreover have "\<dots> \<le> Suc (sum_list (map rsize (rdistinct (map rsimp rs) {})))"
    using without_flts_ineq by blast
  ultimately show "rsize (rsimp (RALTS rs)) \<le> Suc (sum_list (map rsize (rdistinct rs {})))"
    by (meson distinct_simp_ineq order.trans)
qed


lemma larger_acc_smaller_distinct_res:
  shows "(sum_list (map rsize (rdistinct rs ss))) \<ge> (sum_list (map rsize (rdistinct rs (insert a ss))))"
  apply(subgoal_tac "ss \<subseteq> (insert a ss)")
   apply(rule larger_acc_smaller_distinct_res0)
   apply simp
  by (simp add: subset_insertI)

lemma triangle_inequality_distinct:
  shows "sum_list (map rsize (rdistinct (a # rs) ss)) \<le> rsize a + (sum_list (map rsize (rdistinct rs ss)))"
  apply(case_tac "a \<in> ss")
   apply simp
  by (simp add: larger_acc_smaller_distinct_res)


lemma distinct_list_sizeNregex_bounded:
  shows "distinct rs \<and> (\<forall> r \<in> (set rs). rsize r \<le> N) \<Longrightarrow> sum_list (map rsize rs) \<le> N * length rs"
  apply(induct rs)
   apply simp
  by simp


lemma distinct_list_size_len_bounded:
  shows "distinct rs \<and> (\<forall>r \<in> set rs. rsize r \<le> N) \<and> length rs \<le> lrs \<Longrightarrow> sum_list (map rsize rs) \<le> lrs * N "
  by (metis distinct_list_sizeNregex_bounded dual_order.trans mult.commute mult_le_mono1)



lemma rdistinct_same_set:
  shows "(r \<in> set rs) =  (r \<in> set (rdistinct rs {}))"
  apply(induct rs)
   apply simp
  apply(case_tac "a \<in> set rs")
  apply(case_tac "r = a")
    apply (simp)
  apply (simp add: not_mentioned_elem_distinct)
  using not_mentioned_elem_distinct by fastforce



lemma distinct_list_rexp_up_to_certain_size_bouded_by_set_enumerating_up_to_that_size:
  assumes "\<forall>r\<in> set rs. (rsize r) \<le> N"
  shows "sum_list (map rsize (rdistinct rs {})) \<le> (card (sizeNregex N)) * N"
  apply(subgoal_tac "distinct (rdistinct rs {})")
  prefer 2
  using rdistinct_does_the_job apply blast
  apply(subgoal_tac "length (rdistinct rs {}) \<le> card (sizeNregex N)")
  apply(rule distinct_list_size_len_bounded)
   apply(rule conjI)+
    apply simp
   apply(rule conjI)
  using assms
  apply (meson rdistinct_same_set)
   apply blast
  apply(subgoal_tac "\<forall>r \<in> set (rdistinct rs {}). rsize r \<le> N")
   prefer 2
  using assms
   apply (meson rdistinct_same_set)
  apply(subgoal_tac "length (rdistinct rs {}) = card (set (rdistinct rs {}))")
   prefer 2
  apply (simp add: distinct_card)
  apply(simp)
  by (metis card_mono finite_size_n mem_Collect_eq sizeNregex_def subsetI)


lemma star_lambda_form:
  shows "\<forall> r \<in> set (map (\<lambda>s1. RSEQ (rders_simp r0 s1) (RSTAR r0)) ls). 
        \<exists>s2. r = RSEQ (rders_simp r0 s2) (RSTAR r0)"
  by (meson ex_map_conv)


lemma star_lambda_ders:
  assumes "\<forall>s. rsize (rders_simp r0 s) \<le> N"
  shows "\<forall>r\<in>set (map (\<lambda>s1. RSEQ (rders_simp r0 s1) (RSTAR r0)) (star_updates s r0 [[c]])).
            rsize r \<le> Suc (N + rsize (RSTAR r0))"
  using assms star_lambda_form
  apply(simp)
  done




lemma star_control_bounded:
  assumes "\<forall>s. rsize (rders_simp r0 s) \<le> N"
  shows "(sum_list (map rsize (rdistinct (map (\<lambda>s1. RSEQ (rders_simp r0 s1) (RSTAR r0))
         (star_updates s r0 [[c]]) ) {})  ) ) \<le> 
(card (sizeNregex (Suc (N + rsize (RSTAR r0))))) * (Suc (N + rsize (RSTAR r0)))"
  apply(subgoal_tac "\<forall>r \<in> set (map (\<lambda>s1. RSEQ (rders_simp r0 s1) (RSTAR r0))
         (star_updates s r0 [[c]]) ). (rsize r ) \<le> Suc (N + rsize (RSTAR r0))")
   prefer 2
  using star_lambda_ders assms apply blast
  using distinct_list_rexp_up_to_certain_size_bouded_by_set_enumerating_up_to_that_size by blast


lemma star_control_variant:
  assumes "\<forall>s. rsize (rders_simp r0 s) \<le> N"
  shows"Suc 
      (sum_list (map rsize (rdistinct (map (\<lambda>s1. RSEQ (rders_simp r0 s1) (RSTAR r0)) 
          (star_updates list r0 [[a]])) {}))) 
\<le>  (Suc (card (sizeNregex (Suc (N + rsize (RSTAR r0))))) * Suc (N + rsize (RSTAR r0))) "
  apply(subgoal_tac    "(sum_list (map rsize (rdistinct (map (\<lambda>s1. RSEQ (rders_simp r0 s1) (RSTAR r0)) 
          (star_updates list r0 [[a]])) {}))) 
\<le>  ( (card (sizeNregex (Suc (N + rsize (RSTAR r0))))) * Suc (N + rsize (RSTAR r0))) ")
  prefer 2
  using assms star_control_bounded apply presburger
  by simp



lemma star_closed_form_bounded:
  assumes "\<forall>s. rsize (rders_simp r0 s) \<le> N"
  shows "rsize (rders_simp (RSTAR r0) s) \<le> 
            max ((Suc (card (sizeNregex (Suc (N + rsize (RSTAR r0))))) * (Suc (N + rsize (RSTAR r0)))))   (rsize (RSTAR r0))"
  apply(case_tac s)
  apply simp
  apply(subgoal_tac " rsize (rders_simp (RSTAR r0) (a # list)) = 
rsize (rsimp ( RALTS ( (map (\<lambda>s1. RSEQ (rders_simp r0 s1) (RSTAR r0) ) (star_updates list r0 [[a]]) ) )))") 
   prefer 2
  
  using star_closed_form apply presburger
  apply(subgoal_tac "rsize (rsimp (
 RALTS ( (map (\<lambda>s1. RSEQ (rders_simp r0 s1) (RSTAR r0) ) (star_updates list    r0 [[a]]) ) ))) 
\<le>         Suc (sum_list (map rsize (rdistinct (map (\<lambda>s1. RSEQ (rders_simp r0 s1) (RSTAR r0) )
         (star_updates list r0 [[a]]) ) {})  ) )")
  prefer 2
  using alts_simp_control apply presburger
  apply(subgoal_tac "Suc (sum_list 
                 (map rsize
                   (rdistinct (map (\<lambda>s1. RSEQ (rders_simp r0 s1) (RSTAR r0)) (star_updates list r0 [[a]])) {}))) 
\<le>  (Suc (card (sizeNregex (Suc (N + rsize (RSTAR r0))))) * Suc (N + rsize (RSTAR r0)))  ")
  apply auto[1]
  using star_control_variant assms by blast

lemma seq_estimate_bounded: 
  assumes "\<forall>s. rsize (rders_simp r1 s) \<le> N1" 
      and "\<forall>s. rsize (rders_simp r2 s) \<le> N2"
  shows
    "Suc (sum_list (map rsize (rdistinct (RSEQ (rders_simp r1 s) r2 # map (rders_simp r2) (vsuf s r1)) {}))) \<le>
         Suc (Suc (N1 + (rsize r2)) + (N2 * card (sizeNregex N2)))"
proof -
  have a: "sum_list (map rsize (rdistinct (map (rders_simp r2) (vsuf s r1)) {})) \<le> N2 * card (sizeNregex N2)"
    by (metis assms(2) distinct_list_rexp_up_to_certain_size_bouded_by_set_enumerating_up_to_that_size ex_map_conv mult.commute)

  have "sum_list (map rsize (rdistinct (RSEQ (rders_simp r1 s) r2 # map (rders_simp r2) (vsuf s r1)) {})) \<le>
          rsize (RSEQ (rders_simp r1 s) r2) + sum_list (map rsize (rdistinct (map (rders_simp r2) (vsuf s r1)) {}))"
    using triangle_inequality_distinct by blast    
  also have "... \<le> rsize (RSEQ (rders_simp r1 s) r2) + N2 * card (sizeNregex N2)"
    by (simp add: a)
  also have "... \<le> Suc (N1 + (rsize r2) + N2 * card (sizeNregex N2))"
    by (simp add: assms(1))
  finally show ?thesis
    by force
qed    


lemma seq_closed_form_bounded2: 
  assumes "\<forall>s. rsize (rders_simp r1 s) \<le> N1"
  and     "\<forall>s. rsize (rders_simp r2 s) \<le> N2"
shows "rsize (rders_simp (RSEQ r1 r2) s) 
          \<le> max (Suc (Suc (N1 + (rsize r2)) + (N2 * card (sizeNregex N2)))) (rsize (RSEQ r1 r2))"
proof(cases s)
  case Nil
  then show "rsize (rders_simp (RSEQ r1 r2) s)
     \<le> max (Suc (Suc (N1 + rsize r2) + N2 * card (sizeNregex N2))) (rsize (RSEQ r1 r2))" 
    by simp
next
  case (Cons a list)
  then have "rsize (rders_simp (RSEQ r1 r2) s) = 
    rsize (rsimp (RALTS ((RSEQ (rders_simp r1 s) r2) # (map (rders_simp r2) (vsuf s r1)))))" 
  using seq_closed_form_variant by (metis list.discI) 
  also have "... \<le> Suc (sum_list (map rsize (rdistinct (RSEQ (rders_simp r1 s) r2 # map (rders_simp r2) (vsuf s r1)) {})))"
    using alts_simp_control by blast
  also have "... \<le> Suc (Suc (N1 + (rsize r2)) + (N2 * card (sizeNregex N2)))"
  using assms seq_estimate_bounded by blast
  ultimately show "rsize (rders_simp (RSEQ r1 r2) s)
       \<le> max (Suc (Suc (N1 + rsize r2) + N2 * card (sizeNregex N2))) (rsize (RSEQ r1 r2))"
    by auto 
qed


lemma rders_simp_bounded: 
  shows "\<exists>N. \<forall>s. rsize (rders_simp r s) \<le> N"
  apply(induct r)
  apply(rule_tac x = "Suc 0 " in exI)
  using three_easy_cases0 apply force
  using three_easy_cases1 apply blast
  using three_easy_casesC apply blast
  apply(erule exE)+
  apply(rule exI)
  apply(rule allI)
  apply(rule seq_closed_form_bounded2)
  apply(assumption)
  apply(assumption)
  apply (metis alts_closed_form_bounded size_list_estimation')
  using star_closed_form_bounded by blast


unused_thms

end
