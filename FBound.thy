
theory FBound
  imports "BlexerSimp2" "ClosedFormsBounds"
begin



lemma fuse_anything_doesnt_matter:
  shows "rerase a = rerase (fuse bs a)"
  by (smt (verit) fuse.elims rerase.simps(2) rerase.simps(3) rerase.simps(4) rerase.simps(5) rerase.simps(6))


lemma rb_nullability:
  shows "rnullable (rerase a) = bnullable a"
  apply(induct a)
       apply simp+
  done


lemma rerase_preimage:
  shows "rerase r = RZERO \<Longrightarrow> r = AZERO"
  apply(case_tac r)
       apply simp+
  done

lemma rerase_preimage2:
  shows "rerase r = RONE \<Longrightarrow> \<exists>bs. r = AONE bs"
  apply(case_tac r)
       apply simp+
  done

lemma rerase_preimage3:
  shows "rerase r= RCHAR c \<Longrightarrow> \<exists>bs. r = ACHAR bs c"
  apply(case_tac r)
       apply simp+
  done

lemma rerase_preimage4:
  shows "rerase r = RSEQ r1 r2 \<Longrightarrow> \<exists>bs a1 a2. r = ASEQ bs a1 a2 \<and> rerase a1 = r1 \<and> rerase a2 = r2"
  apply(case_tac r)
       apply(simp)+
  done

lemma rerase_preimage5:
  shows "rerase r = RALTS rs \<Longrightarrow> \<exists>bs as. r = AALTs bs as \<and> map rerase as = rs"
  apply(case_tac r)
       apply(simp)+
  done

lemma rerase_preimage6:
  shows "rerase r = RSTAR r0 \<Longrightarrow> \<exists>bs a0. r = ASTAR bs a0 \<and> rerase a0 = r0 "
  apply(case_tac r)
       apply(simp)+
  done

lemma map_rder_bder:
  shows "\<lbrakk> \<And>xa a. \<lbrakk>xa \<in> set x; rerase a = xa\<rbrakk> \<Longrightarrow> rerase (bder c a) = rder c xa;
         map rerase as = x\<rbrakk> \<Longrightarrow>
        map rerase (map (bder c) as) = map (rder c) x"
  apply(induct x arbitrary: as)
   apply simp+
  by force


lemma der_rerase:
  shows "rerase a = r \<Longrightarrow> rerase (bder c a) = rder c r"
  apply(induct r arbitrary: a)
       apply simp
  using rerase_preimage apply fastforce
  using rerase_preimage2 apply force
     apply (metis bder.simps(3) rder.simps(3) rerase.simps(1) rerase.simps(2) rerase_preimage3)
    apply(insert rerase_preimage4)[1]
    apply(subgoal_tac " \<exists>bs a1 a2. a = ASEQ bs a1 a2 \<and> rerase a1 = r1 \<and> rerase a2 = r2")
  prefer 2
     apply presburger
    apply(erule exE)+
    apply(erule conjE)+
    apply(subgoal_tac " rerase (bder c a1) = rder c r1")
  prefer 2
     apply blast
    apply(subgoal_tac " rerase (bder c a2) = rder c r2")
  prefer 2
     apply blast
    apply(case_tac "rnullable r1")
     apply(subgoal_tac "bnullable a1")
  apply simp
  using fuse_anything_doesnt_matter apply presburger
  using rb_nullability apply blast
    apply (metis bder.simps(5) rb_nullability rder.simps(5) rerase.simps(5))
  apply simp
   apply(insert rerase_preimage5)[1]
   apply(subgoal_tac "\<exists>bs as. a = AALTs bs as \<and> map rerase as = x")
  prefer 2
  
    apply blast
   apply(erule exE)+
   apply(erule conjE)+
  apply(subgoal_tac "map rerase (map (bder c) as) = map (rder c) x")
  using bder.simps(4) rerase.simps(4) apply presburger
  using map_rder_bder apply blast
  using fuse_anything_doesnt_matter rerase_preimage6 by force

lemma der_rerase2:
  shows "rerase (bder c a) = rder c (rerase a)"
  using der_rerase by force

lemma rerase_bsimp_ASEQ:
  shows "rerase (bsimp_ASEQ x1 a1 a2) = rsimp_SEQ (rerase a1) (rerase a2)"
  by (smt (verit, ccfv_SIG) BlexerSimp2.bsimp_ASEQ0 BlexerSimp2.bsimp_ASEQ2 basic_rsimp_SEQ_property1 idiot2 basic_rsimp_SEQ_property3 bsimp_ASEQ.simps(1) bsimp_ASEQ1 fuse_anything_doesnt_matter rerase.simps(1) rerase.simps(2) rerase.simps(5) rerase_preimage rerase_preimage2 rsimp_SEQ.simps(1))

lemma rerase_bsimp_AALTs:
  shows "rerase (bsimp_AALTs bs rs) = rsimp_ALTs (map rerase rs)"
  apply(induct rs arbitrary: bs)
   apply simp+
  by (smt (verit, ccfv_threshold) Cons_eq_map_conv bsimp_AALTs.elims fuse_anything_doesnt_matter list.discI list.inject list.simps(9) rerase.simps(4) rsimp_ALTs.elims)


fun anonalt :: "arexp \<Rightarrow> bool"
  where
  "anonalt (AALTs bs2 rs) = False"
| "anonalt r = True"


fun agood :: "arexp \<Rightarrow> bool" where
  "agood AZERO = False"
| "agood (AONE cs) = True" 
| "agood (ACHAR cs c) = True"
| "agood (AALTs cs []) = False"
| "agood (AALTs cs [r]) = False"
| "agood (AALTs cs (r1#r2#rs)) = (distinct (map rerase (r1 # r2 # rs)) \<and>(\<forall>r' \<in> set (r1#r2#rs). agood r' \<and> anonalt r'))"
| "agood (ASEQ _ AZERO _) = False"
| "agood (ASEQ _ (AONE _) _) = False"
| "agood (ASEQ _ _ AZERO) = False"
| "agood (ASEQ cs r1 r2) = (agood r1 \<and> agood r2)"
| "agood (ASTAR cs r) = True"


fun anonnested :: "arexp \<Rightarrow> bool"
  where
  "anonnested (AALTs bs2 []) = True"
| "anonnested (AALTs bs2 ((AALTs bs1 rs1) # rs2)) = False"
| "anonnested (AALTs bs2 (r # rs2)) = anonnested (AALTs bs2 rs2)"
| "anonnested r = True"


lemma asize0:
  shows "0 < asize r"
  apply(induct  r)
       apply(auto)
  done


fun nonazero :: "arexp \<Rightarrow> bool"
  where
  "nonazero AZERO = False"
| "nonazero r = True"

lemma rerase_map_bsimp:
  assumes "\<And> r. r \<in> set x2a \<Longrightarrow> rerase (bsimp r) = (rsimp \<circ> rerase) r"
  shows "  map rerase (map bsimp x2a) =  map (rsimp \<circ> rerase) x2a "
  using assms
  
  apply(induct x2a)
   apply simp
  apply(subgoal_tac "a \<in> set (a # x2a)")
  prefer 2
  apply (meson list.set_intros(1))
  apply(subgoal_tac "rerase (bsimp a ) = (rsimp \<circ> rerase) a")
  apply simp
  by presburger



lemma rerase_flts:
  shows "map rerase (flts rs) = rflts (map rerase rs)"
  apply(induct rs)
   apply simp+
  apply(case_tac a)
       apply simp+
   apply(simp add: rerase_fuse)
  apply simp
  done

lemma rerase_dB:
  shows "map rerase (distinctBy rs rerase acc) = rdistinct (map rerase rs) acc"
  apply(induct rs arbitrary: acc)
   apply simp+
  done
  



lemma rerase_earlier_later_same:
  assumes " \<And>r. r \<in> set x2a \<Longrightarrow> rerase (bsimp r) = rsimp (rerase r)"
  shows " (map rerase (distinctBy (flts (map bsimp x2a)) rerase {})) =
          (rdistinct (rflts (map (rsimp \<circ> rerase) x2a)) {})"
  apply(subst rerase_dB)
  apply(subst rerase_flts)
  apply(subst rerase_map_bsimp)
   apply auto
  using assms
  apply simp
  done



lemma simp_rerase:
  shows "rerase (bsimp a) = rsimp (rerase a)"
  apply(induct  a)
  apply simp+
  using rerase_bsimp_ASEQ apply presburger
  apply simp
   apply(subst rerase_bsimp_AALTs)
  apply(subgoal_tac "map rerase (distinctBy (flts (map bsimp x2a)) rerase {}) =  rdistinct (rflts (map (rsimp \<circ> rerase) x2a)) {}")  
    apply simp
  using rerase_earlier_later_same apply presburger
  apply simp
  done



lemma rders_simp_size:
  shows " rders_simp (rerase r) s  = rerase (bders_simp r s)"
  apply(induct s rule: rev_induct)
   apply simp
  apply(subst rders_simp_append)
  apply(subst bders_simp_append)
  apply(subgoal_tac "rders_simp (rerase r ) xs = rerase (bders_simp r xs)")
   apply(simp only:)
   apply simp
  apply (simp add: der_rerase2 simp_rerase)
  by simp




corollary aders_simp_finiteness:
  assumes "\<exists>N. \<forall>s. rsize (rders_simp (rerase r) s) \<le> N"
  shows " \<exists>N. \<forall>s. asize (bders_simp r s) \<le> N"
  using assms
  apply(subgoal_tac "\<forall>s. asize (bders_simp r s) = rsize (rerase (bders_simp r s))")
   apply(erule exE)
   apply(rule_tac x = "N" in exI)
  using rders_simp_size apply auto[1]
  using asize_rsize by auto
  
theorem annotated_size_bound:
  shows "\<exists>N. \<forall>s. asize (bders_simp r s) \<le> N"
  apply(insert aders_simp_finiteness)
  by (simp add: rders_simp_bounded)


unused_thms

end
