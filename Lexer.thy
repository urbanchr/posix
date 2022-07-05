   
theory Lexer
  imports PosixSpec 
begin

section \<open>The Lexer Functions by Sulzmann and Lu  (without simplification)\<close>

fun 
  mkeps :: "rexp \<Rightarrow> val"
where
  "mkeps(ONE) = Void"
| "mkeps(SEQ r1 r2) = Seq (mkeps r1) (mkeps r2)"
| "mkeps(ALT r1 r2) = (if nullable(r1) then Left (mkeps r1) else Right (mkeps r2))"
| "mkeps(STAR r) = Stars []"
| "mkeps(NTIMES r n) = Stars (replicate n (mkeps r))" 

fun injval :: "rexp \<Rightarrow> char \<Rightarrow> val \<Rightarrow> val"
where
  "injval (CH d) c Void = Char d"
| "injval (ALT r1 r2) c (Left v1) = Left(injval r1 c v1)"
| "injval (ALT r1 r2) c (Right v2) = Right(injval r2 c v2)"
| "injval (SEQ r1 r2) c (Seq v1 v2) = Seq (injval r1 c v1) v2"
| "injval (SEQ r1 r2) c (Left (Seq v1 v2)) = Seq (injval r1 c v1) v2"
| "injval (SEQ r1 r2) c (Right v2) = Seq (mkeps r1) (injval r2 c v2)"
| "injval (STAR r) c (Seq v (Stars vs)) = Stars ((injval r c v) # vs)" 
| "injval (NTIMES r n) c (Seq v (Stars vs)) = Stars ((injval r c v) # vs)" 

fun 
  lexer :: "rexp \<Rightarrow> string \<Rightarrow> val option"
where
  "lexer r [] = (if nullable r then Some(mkeps r) else None)"
| "lexer r (c#s) = (case (lexer (der c r) s) of  
                    None \<Rightarrow> None
                  | Some(v) \<Rightarrow> Some(injval r c v))"



section \<open>Mkeps, Injval Properties\<close>

lemma mkeps_flat:
  assumes "nullable(r)" 
  shows "flat (mkeps r) = []"
using assms
  by (induct rule: mkeps.induct) (auto)

lemma Prf_NTimes_empty:
  assumes "\<forall>v \<in> set vs. \<Turnstile> v : r \<and> flat v = []" 
  and     "length vs = n"
  shows "\<Turnstile> Stars vs : NTIMES r n"
  using assms
  by (metis Prf.intros(7) empty_iff eq_Nil_appendI list.set(1))
  

lemma mkeps_nullable:
  assumes "nullable(r)" 
  shows "\<Turnstile> mkeps r : r"
using assms
  apply (induct rule: mkeps.induct) 
  apply(auto intro: Prf.intros split: if_splits)
  apply (metis Prf.intros(7) append_is_Nil_conv empty_iff list.set(1) list.size(3))
  apply(rule Prf_NTimes_empty)
  apply(auto simp add: mkeps_flat) 
  done

lemma Prf_injval_flat:
  assumes "\<Turnstile> v : der c r" 
  shows "flat (injval r c v) = c # (flat v)"
using assms
apply(induct c r arbitrary: v rule: der.induct)
apply(auto elim!: Prf_elims intro: mkeps_flat split: if_splits)
done

lemma Prf_injval:
  assumes "\<Turnstile> v : der c r" 
  shows "\<Turnstile> (injval r c v) : r"
using assms
apply(induct r arbitrary: c v rule: rexp.induct)
apply(auto intro!: Prf.intros mkeps_nullable elim!: Prf_elims split: if_splits)
(* Star *)
apply(simp add: Prf_injval_flat)
(* NTimes *)
  apply(case_tac x2)
    apply(simp)
  apply(simp)
  apply(subst append.simps(2)[symmetric])
  apply(rule Prf.intros)
  apply(auto simp add: Prf_injval_flat)
  done


text \<open>Mkeps and injval produce, or preserve, Posix values.\<close>


lemma Posix_mkeps:
  assumes "nullable r"
  shows "[] \<in> r \<rightarrow> mkeps r"
using assms
apply(induct r rule: nullable.induct)
apply(auto intro: Posix.intros simp add: nullable_correctness Sequ_def)
apply(subst append.simps(1)[symmetric])
apply(rule Posix.intros)
apply(auto)
by (simp add: Posix_NTIMES2 pow_empty_iff)

lemma Posix_injval:
  assumes "s \<in> (der c r) \<rightarrow> v"
  shows "(c # s) \<in> r \<rightarrow> (injval r c v)"
using assms
proof(induct r arbitrary: s v rule: rexp.induct)
  case ZERO
  have "s \<in> der c ZERO \<rightarrow> v" by fact
  then have "s \<in> ZERO \<rightarrow> v" by simp
  then have "False" by cases
  then show "(c # s) \<in> ZERO \<rightarrow> (injval ZERO c v)" by simp
next
  case ONE
  have "s \<in> der c ONE \<rightarrow> v" by fact
  then have "s \<in> ZERO \<rightarrow> v" by simp
  then have "False" by cases
  then show "(c # s) \<in> ONE \<rightarrow> (injval ONE c v)" by simp
next 
  case (CH d)
  consider (eq) "c = d" | (ineq) "c \<noteq> d" by blast
  then show "(c # s) \<in> (CH d) \<rightarrow> (injval (CH d) c v)"
  proof (cases)
    case eq
    have "s \<in> der c (CH d) \<rightarrow> v" by fact
    then have "s \<in> ONE \<rightarrow> v" using eq by simp
    then have eqs: "s = [] \<and> v = Void" by cases simp
    show "(c # s) \<in> CH d \<rightarrow> injval (CH d) c v" using eq eqs 
    by (auto intro: Posix.intros)
  next
    case ineq
    have "s \<in> der c (CH d) \<rightarrow> v" by fact
    then have "s \<in> ZERO \<rightarrow> v" using ineq by simp
    then have "False" by cases
    then show "(c # s) \<in> CH d \<rightarrow> injval (CH d) c v" by simp
  qed
next
  case (ALT r1 r2)
  have IH1: "\<And>s v. s \<in> der c r1 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r1 \<rightarrow> injval r1 c v" by fact
  have IH2: "\<And>s v. s \<in> der c r2 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r2 \<rightarrow> injval r2 c v" by fact
  have "s \<in> der c (ALT r1 r2) \<rightarrow> v" by fact
  then have "s \<in> ALT (der c r1) (der c r2) \<rightarrow> v" by simp
  then consider (left) v' where "v = Left v'" "s \<in> der c r1 \<rightarrow> v'" 
              | (right) v' where "v = Right v'" "s \<notin> L (der c r1)" "s \<in> der c r2 \<rightarrow> v'" 
              by cases auto
  then show "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c v"
  proof (cases)
    case left
    have "s \<in> der c r1 \<rightarrow> v'" by fact
    then have "(c # s) \<in> r1 \<rightarrow> injval r1 c v'" using IH1 by simp
    then have "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c (Left v')" by (auto intro: Posix.intros)
    then show "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c v" using left by simp
  next 
    case right
    have "s \<notin> L (der c r1)" by fact
    then have "c # s \<notin> L r1" by (simp add: der_correctness Der_def)
    moreover 
    have "s \<in> der c r2 \<rightarrow> v'" by fact
    then have "(c # s) \<in> r2 \<rightarrow> injval r2 c v'" using IH2 by simp
    ultimately have "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c (Right v')" 
      by (auto intro: Posix.intros)
    then show "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c v" using right by simp
  qed
next
  case (SEQ r1 r2)
  have IH1: "\<And>s v. s \<in> der c r1 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r1 \<rightarrow> injval r1 c v" by fact
  have IH2: "\<And>s v. s \<in> der c r2 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r2 \<rightarrow> injval r2 c v" by fact
  have "s \<in> der c (SEQ r1 r2) \<rightarrow> v" by fact
  then consider 
        (left_nullable) v1 v2 s1 s2 where 
        "v = Left (Seq v1 v2)"  "s = s1 @ s2" 
        "s1 \<in> der c r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2" "nullable r1" 
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r1) \<and> s\<^sub>4 \<in> L r2)"
      | (right_nullable) v1 s1 s2 where 
        "v = Right v1" "s = s1 @ s2"  
        "s \<in> der c r2 \<rightarrow> v1" "nullable r1" "s1 @ s2 \<notin> L (SEQ (der c r1) r2)"
      | (not_nullable) v1 v2 s1 s2 where
        "v = Seq v1 v2" "s = s1 @ s2" 
        "s1 \<in> der c r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2" "\<not>nullable r1" 
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r1) \<and> s\<^sub>4 \<in> L r2)"
        by (force split: if_splits elim!: Posix_elims simp add: Sequ_def der_correctness Der_def)   
  then show "(c # s) \<in> SEQ r1 r2 \<rightarrow> injval (SEQ r1 r2) c v" 
    proof (cases)
      case left_nullable
      have "s1 \<in> der c r1 \<rightarrow> v1" by fact
      then have "(c # s1) \<in> r1 \<rightarrow> injval r1 c v1" using IH1 by simp
      moreover
      have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r1) \<and> s\<^sub>4 \<in> L r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> L r1 \<and> s\<^sub>4 \<in> L r2)" by (simp add: der_correctness Der_def)
      ultimately have "((c # s1) @ s2) \<in> SEQ r1 r2 \<rightarrow> Seq (injval r1 c v1) v2" using left_nullable by (rule_tac Posix.intros)
      then show "(c # s) \<in> SEQ r1 r2 \<rightarrow> injval (SEQ r1 r2) c v" using left_nullable by simp
    next
      case right_nullable
      have "nullable r1" by fact
      then have "[] \<in> r1 \<rightarrow> (mkeps r1)" by (rule Posix_mkeps)
      moreover
      have "s \<in> der c r2 \<rightarrow> v1" by fact
      then have "(c # s) \<in> r2 \<rightarrow> (injval r2 c v1)" using IH2 by simp
      moreover
      have "s1 @ s2 \<notin> L (SEQ (der c r1) r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = c # s \<and> [] @ s\<^sub>3 \<in> L r1 \<and> s\<^sub>4 \<in> L r2)" using right_nullable
        by(auto simp add: der_correctness Der_def append_eq_Cons_conv Sequ_def)
      ultimately have "([] @ (c # s)) \<in> SEQ r1 r2 \<rightarrow> Seq (mkeps r1) (injval r2 c v1)"
      by(rule Posix.intros)
      then show "(c # s) \<in> SEQ r1 r2 \<rightarrow> injval (SEQ r1 r2) c v" using right_nullable by simp
    next
      case not_nullable
      have "s1 \<in> der c r1 \<rightarrow> v1" by fact
      then have "(c # s1) \<in> r1 \<rightarrow> injval r1 c v1" using IH1 by simp
      moreover
      have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r1) \<and> s\<^sub>4 \<in> L r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> L r1 \<and> s\<^sub>4 \<in> L r2)" by (simp add: der_correctness Der_def)
      ultimately have "((c # s1) @ s2) \<in> SEQ r1 r2 \<rightarrow> Seq (injval r1 c v1) v2" using not_nullable 
        by (rule_tac Posix.intros) (simp_all) 
      then show "(c # s) \<in> SEQ r1 r2 \<rightarrow> injval (SEQ r1 r2) c v" using not_nullable by simp
    qed
next
  case (STAR r)
  have IH: "\<And>s v. s \<in> der c r \<rightarrow> v \<Longrightarrow> (c # s) \<in> r \<rightarrow> injval r c v" by fact
  have "s \<in> der c (STAR r) \<rightarrow> v" by fact
  then consider
      (cons) v1 vs s1 s2 where 
        "v = Seq v1 (Stars vs)" "s = s1 @ s2" 
        "s1 \<in> der c r \<rightarrow> v1" "s2 \<in> (STAR r) \<rightarrow> (Stars vs)"
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r) \<and> s\<^sub>4 \<in> L (STAR r))" 
        apply(auto elim!: Posix_elims(1-5) simp add: der_correctness Der_def intro: Posix.intros)
        apply(rotate_tac 3)
        apply(erule_tac Posix_elims(6))
        apply (simp add: Posix.intros(6))
        using Posix.intros(7) by blast
    then show "(c # s) \<in> STAR r \<rightarrow> injval (STAR r) c v" 
    proof (cases)
      case cons
          have "s1 \<in> der c r \<rightarrow> v1" by fact
          then have "(c # s1) \<in> r \<rightarrow> injval r c v1" using IH by simp
        moreover
          have "s2 \<in> STAR r \<rightarrow> Stars vs" by fact
        moreover 
          have "(c # s1) \<in> r \<rightarrow> injval r c v1" by fact 
          then have "flat (injval r c v1) = (c # s1)" by (rule Posix1)
          then have "flat (injval r c v1) \<noteq> []" by simp
        moreover 
          have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r) \<and> s\<^sub>4 \<in> L (STAR r))" by fact
          then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> L r \<and> s\<^sub>4 \<in> L (STAR r))" 
            by (simp add: der_correctness Der_def)
        ultimately 
        have "((c # s1) @ s2) \<in> STAR r \<rightarrow> Stars (injval r c v1 # vs)" by (rule Posix.intros)
        then show "(c # s) \<in> STAR r \<rightarrow> injval (STAR r) c v" using cons by(simp)
      qed
next
  case (NTIMES r n)
  have IH: "\<And>s v. s \<in> der c r \<rightarrow> v \<Longrightarrow> (c # s) \<in> r \<rightarrow> injval r c v" by fact
  have "s \<in> der c (NTIMES r n) \<rightarrow> v" by fact
  then consider
      (cons) v1 vs s1 s2 where 
        "v = Seq v1 (Stars vs)" "s = s1 @ s2" 
        "s1 \<in> der c r \<rightarrow> v1" "s2 \<in> (NTIMES r (n - 1)) \<rightarrow> (Stars vs)" "0 < n"
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r) \<and> s\<^sub>4 \<in> L (NTIMES r (n - 1)))" 
    
    apply(auto elim: Posix_elims simp add: der_correctness Der_def intro: Posix.intros split: if_splits)
    apply(erule Posix_elims)
    apply(simp)
    apply(subgoal_tac "\<exists>vss. v2 = Stars vss")
    apply(clarify)
    apply(drule_tac x="vss" in meta_spec)
    apply(drule_tac x="s1" in meta_spec)
    apply(drule_tac x="s2" in meta_spec)
     apply(simp add: der_correctness Der_def)
    apply(erule Posix_elims)
     apply(auto)
      done
    then show "(c # s) \<in> (NTIMES r n) \<rightarrow> injval (NTIMES r n) c v" 
    proof (cases)
      case cons
          have "s1 \<in> der c r \<rightarrow> v1" by fact
          then have "(c # s1) \<in> r \<rightarrow> injval r c v1" using IH by simp
        moreover
          have "s2 \<in> (NTIMES r (n - 1)) \<rightarrow> Stars vs" by fact
        moreover 
          have "(c # s1) \<in> r \<rightarrow> injval r c v1" by fact 
          then have "flat (injval r c v1) = (c # s1)" by (rule Posix1)
          then have "flat (injval r c v1) \<noteq> []" by simp
        moreover 
          have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r) \<and> s\<^sub>4 \<in> L (NTIMES r (n - 1)))" by fact
          then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> L r \<and> s\<^sub>4 \<in> L (NTIMES r (n - 1)))"
            by (simp add: der_correctness Der_def)
        ultimately 
        have "((c # s1) @ s2) \<in> NTIMES r n \<rightarrow> Stars (injval r c v1 # vs)" 
           apply (rule_tac Posix.intros)
               apply(simp_all)
              apply(case_tac n)
            apply(simp)
           using Posix_elims(1) NTIMES.prems apply auto[1]
             apply(simp)
             done
        then show "(c # s) \<in> NTIMES r n \<rightarrow> injval (NTIMES r n) c v" using cons by(simp)
      qed  

qed


section \<open>Lexer Correctness\<close>


lemma lexer_correct_None:
  shows "s \<notin> L r \<longleftrightarrow> lexer r s = None"
  apply(induct s arbitrary: r)
  apply(simp)
  apply(simp add: nullable_correctness)
  apply(simp)
  apply(drule_tac x="der a r" in meta_spec) 
  apply(auto)
  apply(auto simp add: der_correctness Der_def)
done

lemma lexer_correct_Some:
  shows "s \<in> L r \<longleftrightarrow> (\<exists>v. lexer r s = Some(v) \<and> s \<in> r \<rightarrow> v)"
  apply(induct s arbitrary : r)
  apply(simp only: lexer.simps)
  apply(simp)
  apply(simp add: nullable_correctness Posix_mkeps)
  apply(drule_tac x="der a r" in meta_spec)
  apply(simp (no_asm_use) add: der_correctness Der_def del: lexer.simps) 
  apply(simp del: lexer.simps)
  apply(simp only: lexer.simps)
  apply(case_tac "lexer (der a r) s = None")
   apply(auto)[1]
  apply(simp)
  apply(erule exE)
  apply(simp)
  apply(rule iffI)
  apply(simp add: Posix_injval)
  apply(simp add: Posix1(1))
done 

lemma lexer_correctness:
  shows "(lexer r s = Some v) \<longleftrightarrow> s \<in> r \<rightarrow> v"
  and   "(lexer r s = None) \<longleftrightarrow> \<not>(\<exists>v. s \<in> r \<rightarrow> v)"
using Posix1(1) Posix_determ lexer_correct_None lexer_correct_Some apply fastforce
using Posix1(1) lexer_correct_None lexer_correct_Some by blast


subsection {* A slight reformulation of the lexer algorithm using stacked functions*}

fun flex :: "rexp \<Rightarrow> (val \<Rightarrow> val) => string \<Rightarrow> (val \<Rightarrow> val)"
  where
  "flex r f [] = f"
| "flex r f (c#s) = flex (der c r) (\<lambda>v. f (injval r c v)) s"  

lemma flex_fun_apply:
  shows "g (flex r f s v) = flex r (g o f) s v"
  apply(induct s arbitrary: g f r v)
  apply(simp_all add: comp_def)
  by meson

lemma flex_fun_apply2:
  shows "g (flex r id s v) = flex r g s v"
  by (simp add: flex_fun_apply)


lemma flex_append:
  shows "flex r f (s1 @ s2) = flex (ders s1 r) (flex r f s1) s2"
  apply(induct s1 arbitrary: s2 r f)
  apply(simp_all)
  done  

lemma lexer_flex:
  shows "lexer r s = (if nullable (ders s r) 
                      then Some(flex r id s (mkeps (ders s r))) else None)"
  apply(induct s arbitrary: r)
  apply(simp_all add: flex_fun_apply)
  done  

lemma Posix_flex:
  assumes "s2 \<in> (ders s1 r) \<rightarrow> v"
  shows "(s1 @ s2) \<in> r \<rightarrow> flex r id s1 v"
  using assms
  apply(induct s1 arbitrary: r v s2)
  apply(simp)
  apply(simp)  
  apply(drule_tac x="der a r" in meta_spec)
  apply(drule_tac x="v" in meta_spec)
  apply(drule_tac x="s2" in meta_spec)
  apply(simp)
  using  Posix_injval
  apply(drule_tac Posix_injval)
  apply(subst (asm) (5) flex_fun_apply)
  apply(simp)
  done

lemma injval_inj:
  assumes "\<Turnstile> a : (der c r)" "\<Turnstile> v : (der c r)" "injval r c a = injval r c v" 
  shows "a = v"
  using  assms
  apply(induct r arbitrary: a c v)
       apply(auto)
  using Prf_elims(1) apply blast
  using Prf_elims(1) apply blast
     apply(case_tac "c = x")
      apply(auto)
  using Prf_elims(4) apply auto[1]
  using Prf_elims(1) apply blast
    prefer 2
  apply (smt Prf_elims(3) injval.simps(2) injval.simps(3) val.distinct(25) val.inject(3) val.inject(4))
  apply(case_tac "nullable r1")
    apply(auto)
    apply(erule Prf_elims)
     apply(erule Prf_elims)
     apply(erule Prf_elims)
      apply(erule Prf_elims)
      apply(auto)
     apply (metis Prf_injval_flat list.distinct(1) mkeps_flat)
  apply(erule Prf_elims)
     apply(erule Prf_elims)
  apply(auto)
  using Prf_injval_flat mkeps_flat apply fastforce
  apply(erule Prf_elims)
     apply(erule Prf_elims)
   apply(auto)
  apply(erule Prf_elims)
     apply(erule Prf_elims)
  apply(auto)
   apply (smt Prf_elims(6) injval.simps(7) list.inject val.inject(5))
  apply (smt Prf_elims(6) injval.simps(7) list.inject val.inject(5))
  by (smt (verit, best) Prf_elims(1) Prf_elims(2) Prf_elims(7) injval.simps(8) list.inject val.simps(5))
  
  

lemma uu:
  assumes "(c # s) \<in> r \<rightarrow> injval r c v" "\<Turnstile> v : (der c r)"
  shows "s \<in> der c r \<rightarrow> v"
  using assms
  apply -
  apply(subgoal_tac "lexer r (c # s) = Some (injval r c v)")
  prefer 2
  using lexer_correctness(1) apply blast
  apply(simp add: )
  apply(case_tac  "lexer (der c r) s")
   apply(simp)
  apply(simp)
  apply(case_tac "s \<in> der c r \<rightarrow> a")
   prefer 2
   apply (simp add: lexer_correctness(1))
  apply(subgoal_tac "\<Turnstile> a : (der c r)")
   prefer 2
  using Posix1a apply blast
  using injval_inj by blast
  

lemma Posix_flex2:
  assumes "(s1 @ s2) \<in> r \<rightarrow> flex r id s1 v" "\<Turnstile> v : ders s1 r"
  shows "s2 \<in> (ders s1 r) \<rightarrow> v"
  using assms
  apply(induct s1 arbitrary: r v s2 rule: rev_induct)
  apply(simp)
  apply(simp)  
  apply(drule_tac x="r" in meta_spec)
  apply(drule_tac x="injval (ders xs r) x v" in meta_spec)
  apply(drule_tac x="x#s2" in meta_spec)
  apply(simp add: flex_append ders_append)
  using Prf_injval uu by blast

lemma Posix_flex3:
  assumes "s1 \<in> r \<rightarrow> flex r id s1 v" "\<Turnstile> v : ders s1 r"
  shows "[] \<in> (ders s1 r) \<rightarrow> v"
  using assms
  by (simp add: Posix_flex2)

lemma flex_injval:
  shows "flex (der a r) (injval r a) s v = injval r a (flex (der a r) id s v)"
  by (simp add: flex_fun_apply)
  
lemma Prf_flex:
  assumes "\<Turnstile> v : ders s r"
  shows "\<Turnstile> flex r id s v : r"
  using assms
  apply(induct s arbitrary: v r)
  apply(simp)
  apply(simp)
  by (simp add: Prf_injval flex_injval)


unused_thms

end