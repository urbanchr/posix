theory LexerSimp
  imports "Lexer" 
begin

section {* Lexer including some simplifications *}


fun F_RIGHT where
  "F_RIGHT f v = Right (f v)"

fun F_LEFT where
  "F_LEFT f v = Left (f v)"

fun F_ALT where
  "F_ALT f\<^sub>1 f\<^sub>2 (Right v) = Right (f\<^sub>2 v)"
| "F_ALT f\<^sub>1 f\<^sub>2 (Left v) = Left (f\<^sub>1 v)"  
| "F_ALT f1 f2 v = v"


fun F_SEQ1 where
  "F_SEQ1 f\<^sub>1 f\<^sub>2 v = Seq (f\<^sub>1 Void) (f\<^sub>2 v)"

fun F_SEQ2 where 
  "F_SEQ2 f\<^sub>1 f\<^sub>2 v = Seq (f\<^sub>1 v) (f\<^sub>2 Void)"

fun F_SEQ where 
  "F_SEQ f\<^sub>1 f\<^sub>2 (Seq v\<^sub>1 v\<^sub>2) = Seq (f\<^sub>1 v\<^sub>1) (f\<^sub>2 v\<^sub>2)"
| "F_SEQ f1 f2 v = v"

fun simp_ALT where
  "simp_ALT (ZERO, f\<^sub>1) (r\<^sub>2, f\<^sub>2) = (r\<^sub>2, F_RIGHT f\<^sub>2)"
| "simp_ALT (r\<^sub>1, f\<^sub>1) (ZERO, f\<^sub>2) = (r\<^sub>1, F_LEFT f\<^sub>1)"
| "simp_ALT (r\<^sub>1, f\<^sub>1) (r\<^sub>2, f\<^sub>2) = (ALT r\<^sub>1 r\<^sub>2, F_ALT f\<^sub>1 f\<^sub>2)"


fun simp_SEQ where
  "simp_SEQ (ONE, f\<^sub>1) (r\<^sub>2, f\<^sub>2) = (r\<^sub>2, F_SEQ1 f\<^sub>1 f\<^sub>2)"
| "simp_SEQ (r\<^sub>1, f\<^sub>1) (ONE, f\<^sub>2) = (r\<^sub>1, F_SEQ2 f\<^sub>1 f\<^sub>2)"
| "simp_SEQ (ZERO, f\<^sub>1) (r\<^sub>2, f\<^sub>2) = (ZERO, undefined)"
| "simp_SEQ (r\<^sub>1, f\<^sub>1) (ZERO, f\<^sub>2) = (ZERO, undefined)"
| "simp_SEQ (r\<^sub>1, f\<^sub>1) (r\<^sub>2, f\<^sub>2) = (SEQ r\<^sub>1 r\<^sub>2, F_SEQ f\<^sub>1 f\<^sub>2)"  
 
lemma simp_SEQ_simps[simp]:
  "simp_SEQ p1 p2 = (if (fst p1 = ONE) then (fst p2, F_SEQ1 (snd p1) (snd p2))
                    else (if (fst p2 = ONE) then (fst p1, F_SEQ2 (snd p1) (snd p2))
                    else (if (fst p1 = ZERO) then (ZERO, undefined)         
                    else (if (fst p2 = ZERO) then (ZERO, undefined)  
                    else (SEQ (fst p1) (fst p2), F_SEQ (snd p1) (snd p2))))))"
by (induct p1 p2 rule: simp_SEQ.induct) (auto)

lemma simp_ALT_simps[simp]:
  "simp_ALT p1 p2 = (if (fst p1 = ZERO) then (fst p2, F_RIGHT (snd p2))
                    else (if (fst p2 = ZERO) then (fst p1, F_LEFT (snd p1))
                    else (ALT (fst p1) (fst p2), F_ALT (snd p1) (snd p2))))"
by (induct p1 p2 rule: simp_ALT.induct) (auto)

fun 
  simp :: "rexp \<Rightarrow> rexp * (val \<Rightarrow> val)"
where
  "simp (ALT r1 r2) = simp_ALT (simp r1) (simp r2)" 
| "simp (SEQ r1 r2) = simp_SEQ (simp r1) (simp r2)" 
| "simp r = (r, id)"

fun 
  slexer :: "rexp \<Rightarrow> string \<Rightarrow> val option"
where
  "slexer r [] = (if nullable r then Some(mkeps r) else None)"
| "slexer r (c#s) = (let (rs, fr) = simp (der c r) in
                         (case (slexer rs s) of  
                            None \<Rightarrow> None
                          | Some(v) \<Rightarrow> Some(injval r c (fr v))))"


lemma slexer_better_simp:
  "slexer r (c#s) = (case (slexer (fst (simp (der c r))) s) of  
                            None \<Rightarrow> None
                          | Some(v) \<Rightarrow> Some(injval r c ((snd (simp (der c r))) v)))"
by (auto split: prod.split option.split)


lemma L_fst_simp:
  shows "L(r) = L(fst (simp r))"
by (induct r) (auto)

lemma Posix_simp:
  assumes "s \<in> (fst (simp r)) \<rightarrow> v" 
  shows "s \<in> r \<rightarrow> ((snd (simp r)) v)"
using assms
proof(induct r arbitrary: s v rule: rexp.induct)
  case (ALT r1 r2 s v)
  have IH1: "\<And>s v. s \<in> fst (simp r1) \<rightarrow> v \<Longrightarrow> s \<in> r1 \<rightarrow> snd (simp r1) v" by fact
  have IH2: "\<And>s v. s \<in> fst (simp r2) \<rightarrow> v \<Longrightarrow> s \<in> r2 \<rightarrow> snd (simp r2) v" by fact
  have as: "s \<in> fst (simp (ALT r1 r2)) \<rightarrow> v" by fact
  consider (ZERO_ZERO) "fst (simp r1) = ZERO" "fst (simp r2) = ZERO"
         | (ZERO_NZERO) "fst (simp r1) = ZERO" "fst (simp r2) \<noteq> ZERO"
         | (NZERO_ZERO) "fst (simp r1) \<noteq> ZERO" "fst (simp r2) = ZERO"
         | (NZERO_NZERO) "fst (simp r1) \<noteq> ZERO" "fst (simp r2) \<noteq> ZERO" by auto
  then show "s \<in> ALT r1 r2 \<rightarrow> snd (simp (ALT r1 r2)) v" 
    proof(cases)
      case (ZERO_ZERO)
      with as have "s \<in> ZERO \<rightarrow> v" by simp 
      then show "s \<in> ALT r1 r2 \<rightarrow> snd (simp (ALT r1 r2)) v" by (rule Posix_elims(1))
    next
      case (ZERO_NZERO)
      with as have "s \<in> fst (simp r2) \<rightarrow> v" by simp
      with IH2 have "s \<in> r2 \<rightarrow> snd (simp r2) v" by simp
      moreover
      from ZERO_NZERO have "fst (simp r1) = ZERO" by simp
      then have "L (fst (simp r1)) = {}" by simp
      then have "L r1 = {}" using L_fst_simp by simp
      then have "s \<notin> L r1" by simp 
      ultimately have "s \<in> ALT r1 r2 \<rightarrow> Right (snd (simp r2) v)" by (rule Posix_ALT2)
      then show "s \<in> ALT r1 r2 \<rightarrow> snd (simp (ALT r1 r2)) v"
      using ZERO_NZERO by simp
    next
      case (NZERO_ZERO)
      with as have "s \<in> fst (simp r1) \<rightarrow> v" by simp
      with IH1 have "s \<in> r1 \<rightarrow> snd (simp r1) v" by simp
      then have "s \<in> ALT r1 r2 \<rightarrow> Left (snd (simp r1) v)" by (rule Posix_ALT1) 
      then show "s \<in> ALT r1 r2 \<rightarrow> snd (simp (ALT r1 r2)) v" using NZERO_ZERO by simp
    next
      case (NZERO_NZERO)
      with as have "s \<in> ALT (fst (simp r1)) (fst (simp r2)) \<rightarrow> v" by simp
      then consider (Left) v1 where "v = Left v1" "s \<in> (fst (simp r1)) \<rightarrow> v1"
                  | (Right) v2 where "v = Right v2" "s \<in> (fst (simp r2)) \<rightarrow> v2" "s \<notin> L (fst (simp r1))"
                  by (erule_tac Posix_elims(4)) 
      then show "s \<in> ALT r1 r2 \<rightarrow> snd (simp (ALT r1 r2)) v"
      proof(cases)
        case (Left)
        then have "v = Left v1" "s \<in> r1 \<rightarrow> (snd (simp r1) v1)" using IH1 by simp_all
        then show "s \<in> ALT r1 r2 \<rightarrow> snd (simp (ALT r1 r2)) v" using NZERO_NZERO
          by (simp_all add: Posix_ALT1)
      next 
        case (Right)
        then have "v = Right v2" "s \<in> r2 \<rightarrow> (snd (simp r2) v2)" "s \<notin> L r1" using IH2 L_fst_simp by simp_all
        then show "s \<in> ALT r1 r2 \<rightarrow> snd (simp (ALT r1 r2)) v" using NZERO_NZERO
          by (simp_all add: Posix_ALT2)
      qed
    qed
next
  case (SEQ r1 r2 s v)
  have IH1: "\<And>s v. s \<in> fst (simp r1) \<rightarrow> v \<Longrightarrow> s \<in> r1 \<rightarrow> snd (simp r1) v" by fact
  have IH2: "\<And>s v. s \<in> fst (simp r2) \<rightarrow> v \<Longrightarrow> s \<in> r2 \<rightarrow> snd (simp r2) v" by fact
  have as: "s \<in> fst (simp (SEQ r1 r2)) \<rightarrow> v" by fact
  consider (ONE_ONE) "fst (simp r1) = ONE" "fst (simp r2) = ONE"
         | (ONE_NONE) "fst (simp r1) = ONE" "fst (simp r2) \<noteq> ONE"
         | (NONE_ONE) "fst (simp r1) \<noteq> ONE" "fst (simp r2) = ONE"
         | (NONE_NONE) "fst (simp r1) \<noteq> ONE" "fst (simp r2) \<noteq> ONE" 
         by auto
  then show "s \<in> SEQ r1 r2 \<rightarrow> snd (simp (SEQ r1 r2)) v" 
  proof(cases)
      case (ONE_ONE)
      with as have b: "s \<in> ONE \<rightarrow> v" by simp 
      from b have "s \<in> r1 \<rightarrow> snd (simp r1) v" using IH1 ONE_ONE by simp
      moreover
      from b have c: "s = []" "v = Void" using Posix_elims(2) by auto
      moreover
      have "[] \<in> ONE \<rightarrow> Void" by (simp add: Posix_ONE)
      then have "[] \<in> fst (simp r2) \<rightarrow> Void" using ONE_ONE by simp
      then have "[] \<in> r2 \<rightarrow> snd (simp r2) Void" using IH2 by simp
      ultimately have "([] @ []) \<in> SEQ r1 r2 \<rightarrow> Seq (snd (simp r1) Void) (snd (simp r2) Void)"
        using Posix_SEQ by blast 
      then show "s \<in> SEQ r1 r2 \<rightarrow> snd (simp (SEQ r1 r2)) v" using c ONE_ONE by simp
    next
      case (ONE_NONE)
      with as have b: "s \<in> fst (simp r2) \<rightarrow> v" by simp 
      from b have "s \<in> r2 \<rightarrow> snd (simp r2) v" using IH2 ONE_NONE by simp
      moreover
      have "[] \<in> ONE \<rightarrow> Void" by (simp add: Posix_ONE)
      then have "[] \<in> fst (simp r1) \<rightarrow> Void" using ONE_NONE by simp
      then have "[] \<in> r1 \<rightarrow> snd (simp r1) Void" using IH1 by simp
      moreover
      from ONE_NONE(1) have "L (fst (simp r1)) = {[]}" by simp
      then have "L r1 = {[]}" by (simp add: L_fst_simp[symmetric])
      ultimately have "([] @ s) \<in> SEQ r1 r2 \<rightarrow> Seq (snd (simp r1) Void) (snd (simp r2) v)"
        by(rule_tac Posix_SEQ) auto
      then show "s \<in> SEQ r1 r2 \<rightarrow> snd (simp (SEQ r1 r2)) v" using ONE_NONE by simp
    next
      case (NONE_ONE)
        with as have "s \<in> fst (simp r1) \<rightarrow> v" by simp
        with IH1 have "s \<in> r1 \<rightarrow> snd (simp r1) v" by simp
      moreover
        have "[] \<in> ONE \<rightarrow> Void" by (simp add: Posix_ONE)
        then have "[] \<in> fst (simp r2) \<rightarrow> Void" using NONE_ONE by simp
        then have "[] \<in> r2 \<rightarrow> snd (simp r2) Void" using IH2 by simp
      ultimately have "(s @ []) \<in> SEQ r1 r2 \<rightarrow> Seq (snd (simp r1) v) (snd (simp r2) Void)"
        by(rule_tac Posix_SEQ) auto
      then show "s \<in> SEQ r1 r2 \<rightarrow> snd (simp (SEQ r1 r2)) v" using NONE_ONE by simp
    next
      case (NONE_NONE)
      from as have 00: "fst (simp r1) \<noteq> ZERO" "fst (simp r2) \<noteq> ZERO" 
        apply(auto)
        apply(smt Posix_elims(1) fst_conv)
        by (smt NONE_NONE(2) Posix_elims(1) fstI)
      with NONE_NONE as have "s \<in> SEQ (fst (simp r1)) (fst (simp r2)) \<rightarrow> v" by simp
      then obtain s1 s2 v1 v2 where eqs: "s = s1 @ s2" "v = Seq v1 v2"
                     "s1 \<in> (fst (simp r1)) \<rightarrow> v1" "s2 \<in> (fst (simp r2)) \<rightarrow> v2"
                     "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L r1 \<and> s\<^sub>4 \<in> L r2)"
                     by (erule_tac Posix_elims(5)) (auto simp add: L_fst_simp[symmetric]) 
      then have "s1 \<in> r1 \<rightarrow> (snd (simp r1) v1)" "s2 \<in> r2 \<rightarrow> (snd (simp r2) v2)"
        using IH1 IH2 by auto             
      then show "s \<in> SEQ r1 r2 \<rightarrow> snd (simp (SEQ r1 r2)) v" using eqs NONE_NONE 00
        by(auto intro: Posix_SEQ)
    qed
qed (simp_all)


lemma slexer_correctness:
  shows "slexer r s = lexer r s"
proof(induct s arbitrary: r)
  case Nil
  show "slexer r [] = lexer r []" by simp
next 
  case (Cons c s r)
  have IH: "\<And>r. slexer r s = lexer r s" by fact
  show "slexer r (c # s) = lexer r (c # s)" 
   proof (cases "s \<in> L (der c r)")
     case True
       assume a1: "s \<in> L (der c r)"
       then obtain v1 where a2: "lexer (der c r) s = Some v1" "s \<in> der c r \<rightarrow> v1"
         using lexer_correct_Some by auto
       from a1 have "s \<in> L (fst (simp (der c r)))" using L_fst_simp[symmetric] by simp
       then obtain v2 where a3: "lexer (fst (simp (der c r))) s = Some v2" "s \<in> (fst (simp (der c r))) \<rightarrow> v2"
          using lexer_correct_Some by auto
       then have a4: "slexer (fst (simp (der c r))) s = Some v2" using IH by simp
       from a3(2) have "s \<in> der c r \<rightarrow> (snd (simp (der c r))) v2" using Posix_simp by simp
       with a2(2) have "v1 = (snd (simp (der c r))) v2" using Posix_determ by simp
       with a2(1) a4 show "slexer r (c # s) = lexer r (c # s)" by (auto split: prod.split)
     next 
     case False
       assume b1: "s \<notin> L (der c r)"
       then have "lexer (der c r) s = None" using lexer_correct_None by simp
       moreover
       from b1 have "s \<notin> L (fst (simp (der c r)))" using L_fst_simp[symmetric] by simp
       then have "lexer (fst (simp (der c r))) s = None" using lexer_correct_None by simp
       then have "slexer (fst (simp (der c r))) s = None" using IH by simp
       ultimately show "slexer r (c # s) = lexer r (c # s)" 
         by (simp del: slexer.simps add: slexer_better_simp)
   qed
 qed  


unused_thms


end