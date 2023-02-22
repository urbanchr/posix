// Dearivative-based lexer using Brzozowski derivatives
// and BitCode annotations from Sulzmann and Lu
//
//   tested with 
//
//     Ammonite Repl 2.5.6 (Scala 2.13.10 Java 17.0.1)
//
//   call with
//
//   amm re-bit.sc 
//
//   

import scala.language.implicitConversions    
import scala.language.reflectiveCalls
import scala.annotation.tailrec   

// standard regular expressions including n-times
abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class NTIMES(r: Rexp, n: Int) extends Rexp

abstract class Bit
case object Z extends Bit
case object S extends Bit

type Bits = List[Bit]

// annotated regular expressions
abstract class ARexp 
case object AZERO extends ARexp
case class AONE(bs: Bits) extends ARexp
case class ACHAR(bs: Bits, c: Char) extends ARexp
case class AALTS(bs: Bits, rs: List[ARexp]) extends ARexp 
case class ASEQ(bs: Bits, r1: ARexp, r2: ARexp) extends ARexp 
case class ASTAR(bs: Bits, r: ARexp) extends ARexp 
case class ANTIMES(bs: Bits, r: ARexp, n: Int) extends ARexp 


// an abbreviation for binary alternatives
def AALT(bs: Bits, r1: ARexp, r2: ARexp) = AALTS(bs, List(r1, r2))

// values
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val

   
// some convenience for typing in regular expressions
def charlist2rexp(s: List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s: String) : Rexp = charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}

implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
}


// some helper functions
//=======================

//erase function: extracts the Rexp from ARexp
def erase(r:ARexp): Rexp = r match{
  case AZERO => ZERO
  case AONE(_) => ONE
  case ACHAR(bs, c) => CHAR(c)
  case AALTS(bs, Nil) => ZERO
  case AALTS(bs, r::Nil) => erase(r)
  case AALTS(bs, r::rs) => ALT(erase(r), erase(AALTS(bs, rs)))
  case ASEQ(bs, r1, r2) => SEQ (erase(r1), erase(r2))
  case ASTAR(cs, ASTAR(ds, r)) => STAR(erase(r))
  case ASTAR(cs, r) => STAR(erase(r))
  case ANTIMES(cs, r, n) => NTIMES(erase(r), n)
}

// adds (fuses) a bitsequence to an arexp
def fuse(bs: Bits, r: ARexp) : ARexp = r match {
  case AZERO => AZERO
  case AONE(cs) => AONE(bs ++ cs)
  case ACHAR(cs, c) => ACHAR(bs ++ cs, c)
  case AALTS(cs, rs) => AALTS(bs ++ cs, rs)
  case ASEQ(cs, r1, r2) => ASEQ(bs ++ cs, r1, r2)
  case ASTAR(cs, r) => ASTAR(bs ++ cs, r)
  case ANTIMES(cs, r, n) => ANTIMES(bs ++ cs, r, n)
}

// internalises a "normal" regex into an annotated regex
def internalise(r: Rexp) : ARexp = r match {
  case ZERO => AZERO
  case ONE => AONE(Nil)
  case CHAR(c) => ACHAR(Nil, c)
  case ALT(r1, r2) => AALT(Nil, fuse(List(Z), internalise(r1)), 
			                          fuse(List(S), internalise(r2)))
  case SEQ(r1, r2) => ASEQ(Nil, internalise(r1), internalise(r2))
  case STAR(r) => ASTAR(Nil, internalise(r))
  case NTIMES(r, n) => ANTIMES(Nil, internalise(r), n)
}


// decoding of a value from a bitsequence
def decode_aux(r: Rexp, bs: Bits) : (Val, Bits) = {
  //println(s"bits: ${bs.length}  $r")
  (r, bs) match {
  case (ONE, bs) => (Empty, bs)
  case (CHAR(c), bs) => (Chr(c), bs)
  case (ALT(r1, r2), Z::bs) => {
    val (v, bs1) = decode_aux(r1, bs)
    (Left(v), bs1)
  }
  case (ALT(r1, r2), S::bs) => {
    val (v, bs1) = decode_aux(r2, bs)
    (Right(v), bs1)
  }
  case (SEQ(r1, r2), bs) => {
    val (v1, bs1) = decode_aux(r1, bs)
    val (v2, bs2) = decode_aux(r2, bs1)
    (Sequ(v1, v2), bs2)
  }
  case (STAR(r1), Z::bs) => {
    val (v, bs1) = decode_aux(r1, bs)
    val (Stars(vs), bs2) = decode_aux(STAR(r1), bs1)
    (Stars(v::vs), bs2)
  }
  case (STAR(_), S::bs) => (Stars(Nil), bs)
  case (NTIMES(r1, n), bs) => decode_aux(STAR(r1), bs)
}}

/*
def decode(r: Rexp, bs: Bits) = decode_aux(r, bs) match {
  case (v, Nil) => v
  case _ => throw new Exception("Not decodable")
}
*/


// for larger examples the simple decoding function above
// unfortunately stack-overflows
// 
// decode2 below is the CPS-translated version of decode_aux,
// unfortunately Scala does not recognise this version as 
// tail-recursive and it also stack-overflows
//
// therefore we have to do some contortions to work around
// the limitations of Scala (and the JVM)

//@tailrec
def decode2(r: Rexp, bs: Bits, k: (Val, Bits) => (Val, Bits)) : (Val, Bits) = 
  (r, bs) match {
  case (ONE, bs) => k(Empty, bs)
  case (CHAR(c), bs) => k(Chr(c), bs)
  case (ALT(r1, r2), Z::bs) => 
    decode2(r1, bs, (v, bs) => k(Left(v), bs))
  case (ALT(r1, r2), S::bs) => 
    decode2(r1, bs, (v, bs) => k(Right(v), bs))
  case (SEQ(r1, r2), bs) => 
    decode2(r1, bs, (v1, bs1) => 
      decode2(r2, bs1, (v2, bs2) => k(Sequ(v1, v2), bs2)))
  case (STAR(_), S::bs) => k(Stars(Nil), bs) 
  case (STAR(r1), Z::bs) => 
    decode2(r1, bs, (v, bs1) => 
       decode2(STAR(r1), bs1, { case (Stars(vs), bs2) => k(Stars(v::vs), bs2) }))
  case (NTIMES(_, _), S::bs) => k(Stars(Nil), bs)
  case (NTIMES(r1, n), Z::bs) => 
    decode2(r1, bs, (v, bs1) =>
       decode2(NTIMES(r1, n - 1), bs1, { case (Stars(vs), bs2) => k(Stars(v::vs), bs2) }))
}

// we first defunctionalize the CPS-version, this is
// inspired by the very nice paper "Defunctionalization at Work"
// by Danvy and Nielsen.

// this is an encoding of the continuation
abstract class RegStack
case object CEMPTY extends RegStack
case class CLEFT(k: RegStack) extends RegStack
case class CRIGHT(k: RegStack) extends RegStack
case class CSEQ1(r: Rexp, k: RegStack) extends RegStack
case class CSEQ2(v: Val, k: RegStack) extends RegStack
case class CSTARS(r: Rexp, vs: List[Val], k: RegStack) extends RegStack


def decode3(r: Rexp, bs: Bits, k: RegStack) : (Val, Bits) = {
  //println(s"decode: $r $bs $k")
  (r, bs) match {
  case (ONE, bs) => pop_and_decode(k, Empty, bs)
  case (CHAR(c), bs) => pop_and_decode(k, Chr(c), bs)
  case (ALT(r1, r2), Z::bs) => decode3(r1, bs, CLEFT(k))
  case (ALT(r1, r2), S::bs) => decode3(r2, bs, CRIGHT(k))
  case (SEQ(r1, r2), bs) => decode3(r1, bs, CSEQ1(r2, k))
  case (STAR(_), S::bs) => pop_and_decode(k, Stars(Nil), bs) 
  case (STAR(r1), Z::bs) => decode3(r1, bs, CSTARS(r1, Nil, k))
  case (NTIMES(r, _), bs) => decode3(STAR(r), bs, k)
}}

def pop_and_decode(k: RegStack, v: Val, bs: Bits) : (Val, Bits) = {
  //println(s"pop: $k $v $bs") 
  k match {
  case CEMPTY => (v, bs)
  case CLEFT(rest) => pop_and_decode(rest, Left(v), bs)
  case CRIGHT(rest) => pop_and_decode(rest, Right(v), bs)
  case CSEQ1(r2, rest) => decode3(r2, bs, CSEQ2(v, rest))
  case CSEQ2(v1, rest) => pop_and_decode(rest, Sequ(v1, v), bs)
  case CSTARS(r1, vs, rest) => bs match {
    case S::bs => pop_and_decode(rest, Stars(vs :+ v), bs)
    case Z::bs => decode3(r1, bs, CSTARS(r1, vs :+ v, rest))
  }
}}

// now the version above is stack-safe in any other FP language,
// but Scala still does not cooperate because it does not optimise
// mutual recursive function calls; therefore the contortions below
// to twist it into a single function

abstract class Call 
case class Dec(r: Rexp, bs: Bits, k: RegStack) extends Call
case class Pop(k: RegStack, v: Val, bs: Bits) extends Call

@tailrec
def de3(c: Call) : (Val, Bits) = c match {
  case Dec(r: Rexp, bs: Bits, k: RegStack) => {
    (r, bs) match {
    case (ONE, bs) => de3(Pop(k, Empty, bs))
    case (CHAR(c), bs) => de3(Pop(k, Chr(c), bs))
    case (ALT(r1, r2), Z::bs) => de3(Dec(r1, bs, CLEFT(k)))
    case (ALT(r1, r2), S::bs) => de3(Dec(r2, bs, CRIGHT(k)))
    case (SEQ(r1, r2), bs) => de3(Dec(r1, bs, CSEQ1(r2, k)))
    case (STAR(_), S::bs) => de3(Pop(k, Stars(Nil), bs)) 
    case (STAR(r1), Z::bs) => de3(Dec(r1, bs, CSTARS(r1, Nil, k)))
    case (NTIMES(r, _), bs) => de3(Dec(STAR(r), bs, k))
    }
  }
  case Pop(k: RegStack, v: Val, bs: Bits) => {
    k match {
      case CEMPTY => (v, bs)
      case CLEFT(rest) => de3(Pop(rest, Left(v), bs))
      case CRIGHT(rest) => de3(Pop(rest, Right(v), bs))
      case CSEQ1(r2, rest) => de3(Dec(r2, bs, CSEQ2(v, rest)))
      case CSEQ2(v1, rest) => de3(Pop(rest, Sequ(v1, v), bs))
      case CSTARS(r1, vs, rest) => bs match {
        case S::bs => de3(Pop(rest, Stars(vs :+ v), bs))
        case Z::bs => de3(Dec(r1, bs, CSTARS(r1, vs :+ v, rest)))
      }
    }
  }
}

// decoding is now truly tail-recursive

def decode(r: Rexp, bs: Bits) = de3(Dec(r, bs, CEMPTY)) match {
  case (v, Nil) => v
  case _ => throw new Exception("Not decodable")
}


// the code for a value
def code(v: Val) : Bits = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => Z :: code(v)
  case Right(v) => S :: code(v)
  case Sequ(v1, v2) => code(v1) ::: code(v2)
  case Stars(Nil) => List(S)
  case Stars(v::vs) =>  Z :: code(v) ::: code(Stars(vs))
}


// nullable function: tests whether the an (annotated) 
// regular expression can recognise the empty string
def bnullable (r: ARexp) : Boolean = r match {
  case AZERO => false
  case AONE(_) => true
  case ACHAR(_,_) => false
  case AALTS(_, rs) => rs.exists(bnullable)
  case ASEQ(_, r1, r2) => bnullable(r1) && bnullable(r2)
  case ASTAR(_, _) => true
  case ANTIMES(_, r, n) => if (n == 0) true else bnullable(r)
}

// generates a bitsequence for how the derivative matches the
// empty string
def bmkeps(r: ARexp) : Bits = r match {
  case AONE(bs) => bs
  case AALTS(bs, r::Nil) => bs ++ bmkeps(r) 
  case AALTS(bs, r::rs) => 
    if (bnullable(r)) bs ++ bmkeps(r) else bmkeps(AALTS(bs, rs))  
  case ASEQ(bs, r1, r2) => bs ++ bmkeps(r1) ++ bmkeps(r2)
  case ASTAR(bs, r) => bs ++ List(S)
  case ANTIMES(bs, r, 0) => bs ++ List(S)
  case ANTIMES(bs, r, n) => bs ++ List(Z) ++ bmkeps(r) ++ bmkeps(ANTIMES(Nil, r, n - 1))
}

// derivative of a regular expression w.r.t. a character
def bder(c: Char, r: ARexp) : ARexp = r match {
  case AZERO => AZERO
  case AONE(_) => AZERO
  case ACHAR(bs, d) => if (c == d) AONE(bs) else AZERO
  case AALTS(bs, rs) => AALTS(bs, rs.map(bder(c, _)))
  case ASEQ(bs, r1, r2) => 
    if (bnullable(r1)) AALT(bs, ASEQ(Nil, bder(c, r1), r2), fuse(bmkeps(r1), bder(c, r2)))
    else ASEQ(bs, bder(c, r1), r2)
  case ASTAR(bs, r) => ASEQ(bs ++ List(Z), bder(c, r), ASTAR(Nil, r))
  case ANTIMES(bs, r, n) => 
    if (n == 0) AZERO else ASEQ(bs ++ List(Z), bder(c, r), ANTIMES(Nil, r, n - 1))
}

// derivative w.r.t. a string (iterates bder)
@tailrec
def bders (r: ARexp, s: List[Char]) : ARexp = s match {
  case Nil => r
  case c::s => bders(bder(c, r), s)
}

// unsimplified lexing function (produces a value without simplification)
def blex(r: ARexp, s: List[Char]) : Bits = s match {
  case Nil => if (bnullable(r)) bmkeps(r) else throw new Exception("Not matched")
  case c::cs => blex(bder(c, r), cs)
}

def blexer(r: Rexp, s: String) : Val = 
  decode(r, blex(internalise(r), s.toList))


//=======================
// simplification 


def flts(rs: List[ARexp]) : List[ARexp] = rs match {
  case Nil => Nil
  case AZERO :: rs => flts(rs)
  case AALTS(bs, rs1) :: rs => rs1.map(fuse(bs, _)) ++ flts(rs)
  case r1 :: rs => r1 :: flts(rs)
}


def distinctWith[B](xs: List[B], 
                    eq: (B, B) => Boolean, 
                    acc: List[B] = Nil): List[B] = xs match {
  case Nil => Nil
  case x::xs => {
    if (acc.exists(eq(_, x))) distinctWith(xs, eq, acc)
    else x::distinctWith(xs, eq, x::acc)
  }
} 


// equivalence
def eqm(r1: ARexp, r2: ARexp) : Boolean = (r1, r2) match {
  case (AZERO, AZERO) => true
  case (AONE(_), AONE(_)) => true
  case (ACHAR(_, c), ACHAR(_, d)) => c == d
  case (ASEQ(_, ra1, ra2), ASEQ(_, rb1, rb2)) => eqm(ra1, rb1) && eqm(ra2, rb2)
  case (AALTS(_, Nil), AALTS(_, Nil)) => true
  case (AALTS(_, r1::rs1), AALTS(_, r2::rs2)) => eqm(r1, r2) && eqm(AALTS(Nil, rs1), AALTS(Nil, rs2))
  case (ASTAR(_, r1), ASTAR(_, r2)) => eqm(r1, r2)
  case (ANTIMES(_, r1, n1), ANTIMES(_, r2, n2)) => n1 == n2 && eqm(r1, r2)
  case _ => false
}


def bsimp(r: ARexp): ARexp = r match {
  case ASEQ(bs1, r1, r2) => (bsimp(r1), bsimp(r2)) match {
      case (AZERO, _) => AZERO
      case (_, AZERO) => AZERO
      case (AONE(bs2), r2s) => fuse(bs1 ++ bs2, r2s)
      // desroys POSIX property
      //case (AALTS(bs2, rs), r2s) => AALTS(bs1 ::: bs2, rs.map(ASEQ(Nil, _, r2s)))
      case (r1s, r2s) => ASEQ(bs1, r1s, r2s)
  }
  case AALTS(bs1, rs) => 
    distinctWith[ARexp](flts(rs.map(bsimp)), 
                        (r1: ARexp, r2: ARexp) => eqm(r1, r2) ) match {  
      case Nil => AZERO
      case r::Nil => fuse(bs1, r)
      case rs => AALTS(bs1, rs)
  }
  //case ANTIMES(bs, _, 0) => AONE(bs)
  case r => r
}

def bders_simp(r: ARexp, s: List[Char]) : ARexp = s match {
  case Nil => r
  case c::cs => bders_simp(bsimp(bder(c, r)), cs)
}


def blex_simp(r: ARexp, s: List[Char]) : Bits = s match {
  case Nil => if (bnullable(r)) bmkeps(r) 
              else throw new Exception("Not matched")
  case c::cs => blex_simp(bsimp(bder(c, r)), cs)
}

def blexer_simp(r: Rexp, s: String) : Val = 
  decode(r, blex_simp(internalise(r), s.toList))


// extracts a string from value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
}


def size(r: Rexp): Int = r match {
  case ZERO => 1
  case ONE => 1
  case CHAR(_) => 1
  case ALT(r1, r2) => 1 + size(r1) + size (r2)
  case SEQ(r1, r2) => 1 + size(r1) + size (r2)
  case STAR(r1) => 1 + size(r1)
  case NTIMES(r1, n) => 1 + size(r1)
}

def asize(r: ARexp): Int = r match {
  case AZERO => 1
  case AONE(_) => 1
  case ACHAR(_, _) => 1
  case AALTS(_, rs) => 1 + rs.map(asize).sum
  case ASEQ(_, r1, r2) => 1 + asize(r1) + asize(r2)
  case ASTAR(_, r1) => 1 + asize(r1)
  case ANTIMES(_, r1, n) => 1 + asize(r1)
}

// some pretty printing for values

// function that counts occurences of elements in a list
@tailrec
def cnt(xs: List[String], acc: List[(String, Int)] = Nil) : List[(String, Int)] = 
  (xs, acc) match { 
  case (Nil, acc) => acc.reverse
  case (x::xs, Nil) => cnt(xs, (x, 1)::Nil)
  case (x::xs, (y, n)::ys) =>  
    if (x == y) cnt(xs, (y, n + 1)::ys)
    else cnt(xs, (x, 1)::(y, n)::ys)
}

def p_pair(x_n: (String, Int)) = 
  if (x_n._2 == 1) x_n._1 else s"${x_n._1} x ${x_n._2}"

def pretty_list(ss: List[String]) : String = ss match {
  case Nil => ""
  case s::Nil => s 
  case s::ss => s"$s, ${pretty_list(ss)}"
}

def pretty(v: Val) : String = v match {
  case Empty => "Empty"
  case Chr(c) => s"$c"
  case Sequ(v1, v2) => s"Sequ(${pretty(v1)},${pretty(v2)})"
  case Left(v) => s"Left(${pretty(v)})"
  case Right(v) => s"Right(${pretty(v)})"
  case Stars(vs) => { 
      val vss = vs.map(pretty)
      val css = cnt(vss)
      val vss2 = css.map(p_pair) 
      s"Stars(${pretty_list(vss2)})" 
  } 
}

// pretty printing for annotated regexes

def pp2(bs: Bits) = "[]" //bs.mkString("[", ",", "]")

def pp(r:ARexp): String = r match{
  case AZERO => "AZERO"
  case AONE(bs) => s"AONE(${pp2(bs)})"
  case ACHAR(bs, c) => s"ACHAR(${pp2(bs)},$c)"
  case AALTS(bs, rs) => s"ALTS(${pp2(bs)}, ${rs.map(pp).mkString(",")})"
  case ASEQ(bs, r1, r2) => s"ASEQ(${pp2(bs)},${pp(r1)},${pp(r2)})"
  case ASTAR(cs, r) => s"ASTAR(${pp2(cs)},${pp(r)})" 
  case ANTIMES(cs, r, n) => s"ANT(${pp2(cs)},${pp(r)},$n)"
}



// Test cases
// ==========


def time_needed[T](n: Int, code: => T) = {
  val start = System.nanoTime()
  for (i <- 0 until n) code
  val end = System.nanoTime()
  (end - start)/(n * 1.0e9)
}

/*
val reg = ("a" | "ab") ~ ("b" | "") 
val str = "ab"

println(bders(internalise(reg), str.toList))         
println(bsimp(bders(internalise(reg), str.toList)))  
println(bders_simp(internalise(reg), str.toList))    
println(blexer(reg, str))
println(blexer_simp(reg, str)) // Sequ(Right(Sequ(Chr(a),Chr(b))),Right(Empty))

println("\nStar Tests:")

val reg1 = STAR("a" | "b")
val str1 = "aaba"
println(bders_simp(internalise(reg1), str1.toList))
println(bmkeps(bders_simp(internalise(reg1), str1.toList)))
println(blexer_simp(reg1, str1))
*/

@main
def test1() = {
  
  val reg = STAR("a" | "aa")
  val areg = internalise(reg)
  println(s"Star Test: ${reg}")

  println(asize(bders_simp(areg, ("a" * 0).toList)))
  println(asize(bders_simp(areg, ("a" * 1).toList)))
  println(asize(bders_simp(areg, ("a" * 2).toList)))
  println(asize(bders_simp(areg, ("a" * 3).toList)))
  println(asize(bders_simp(areg, ("a" * 4).toList)))
  println(asize(bders_simp(areg, ("a" * 50000).toList)))

  println(pretty(blexer_simp(reg, "a" * 50001)))
}


@main
def test2() = {

  val reg = STAR("a" | "aa")
  println(s"Star Test: ${reg}")

  println(time_needed(10, blexer_simp(reg, "a" * 10001)))

  println("\nN-Times Test:")

  val nr = NTIMES(NTIMES("a", 200), 200)
  val nreg = SEQ(nr, STAR("a"))
  val nstr = "a" * 50000

  println(pretty(blexer_simp(nreg, nstr)))
  println(time_needed(10, blexer_simp(nreg, nstr)))
}
