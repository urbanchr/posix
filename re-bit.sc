// Dearivative-based lexer using Brzozowski derivatives
//
//   tested with 
//
//     Ammonite Repl 2.5.3 (Scala 2.13.8 Java 17.0.1)
//     Scala 2.13.6 (OpenJDK 64-Bit Server VM, Java 17.0.1)
//
//   call with
//
//   amm re-bit.sc     or   scala re-bit.sc
//
//   

import scala.language.implicitConversions    
import scala.language.reflectiveCalls
import scala.annotation.tailrec   

// standard regular expressions
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


// Bitcoded + Annotation
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

def fuse(bs: Bits, r: ARexp) : ARexp = r match {
  case AZERO => AZERO
  case AONE(cs) => AONE(bs ++ cs)
  case ACHAR(cs, c) => ACHAR(bs ++ cs, c)
  case AALTS(cs, rs) => AALTS(bs ++ cs, rs)
  case ASEQ(cs, r1, r2) => ASEQ(bs ++ cs, r1, r2)
  case ASTAR(cs, r) => ASTAR(bs ++ cs, r)
  case ANTIMES(cs, r, n) => ANTIMES(bs ++ cs, r, n)
}

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
def decode_aux(r: Rexp, bs: Bits) : (Val, Bits) = (r, bs) match {
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
  case (NTIMES(r1, n), Z::bs) => {
    val (v, bs1) = decode_aux(r1, bs)
    val (Stars(vs), bs2) = decode_aux(NTIMES(r1, n - 1), bs1)
    (Stars(v::vs), bs2)
  }
  case (NTIMES(_, _), S::bs) => (Stars(Nil), bs)
}

def decode(r: Rexp, bs: Bits) = decode_aux(r, bs) match {
  case (v, Nil) => v
  case _ => throw new Exception("Not decodable")
}

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

def bmkeps(r: ARexp) : Bits = r match {
  case AONE(bs) => bs
  case AALTS(bs, r::Nil) => bs ++ bmkeps(r) 
  case AALTS(bs, r::rs) => 
    if (bnullable(r)) bs ++ bmkeps(r) else bmkeps(AALTS(bs, rs))  
  case ASEQ(bs, r1, r2) => bs ++ bmkeps(r1) ++ bmkeps(r2)
  case ASTAR(bs, r) => bs ++ List(S)
  case ANTIMES(bs, r, 0) => bs ++ List(S)
  case ANTIMES(bs, r, n) => bs ++ List(S) ++ bmkeps(r) ++ bmkeps(ANTIMES(Nil, r, n - 1))
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

// unsimplified lexing function (produces a value)
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
def eq(r1: ARexp, r2: ARexp) : Boolean = (r1, r2) match {
  case (AZERO, AZERO) => true
  case (AONE(_), AONE(_)) => true
  case (ACHAR(_, c), ACHAR(_, d)) => c == d
  case (ASEQ(_, ra1, ra2), ASEQ(_, rb1, rb2)) => eq(ra1, rb1) && eq(ra2, rb2)
  case (AALTS(_, Nil), AALTS(_, Nil)) => true
  case (AALTS(_, r1::rs1), AALTS(_, r2::rs2)) => eq(r1, r2) && eq(AALTS(Nil, rs1), AALTS(Nil, rs2))
  case (ASTAR(_, r1), ASTAR(_, r2)) => eq(r1, r2)
  case (ANTIMES(_, r1, n1), ANTIMES(_, r2, n2)) => n1 == n2 && eq(r1, r2)
  case _ => false
}


def bsimp(r: ARexp): ARexp = r match {
  case ASEQ(bs1, r1, r2) => (bsimp(r1), bsimp(r2)) match {
      case (AZERO, _) => AZERO
      case (_, AZERO) => AZERO
      case (AONE(bs2), r2s) => fuse(bs1 ++ bs2, r2s)
      case (r1s, r2s) => ASEQ(bs1, r1s, r2s)
  }
  case AALTS(bs1, rs) => distinctWith(flts(rs.map(bsimp)), eq) match {  
      case Nil => AZERO
      case r::Nil => fuse(bs1, r)
      case rs => AALTS(bs1, rs)
  }
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

def asize(r: ARexp) : Int = size(erase(r)) 

// Test case

val reg = ("a" | "ab") ~ ("c" | "bc") 
val str = "abc"

println(bders(internalise(reg), str.toList))         // AONE(List(Z, S))
println(bsimp(bders(internalise(reg), str.toList)))  // AONE(List(Z, S))
println(bders_simp(internalise(reg), str.toList))  // AONE(List(Z, S))
println(blexer(reg, str))
println(blexer_simp(reg, str)) // Sequ(Left(Chr(a)),Right(Sequ(Chr(b),Chr(c))))


/*
val TEST = STAR("a" | "aa")



println(asize(bders_simp(internalise(TEST), ("a" * 0).toList)))
println(asize(bders_simp(internalise(TEST), ("a" * 1).toList)))
println(asize(bders_simp(internalise(TEST), ("a" * 2).toList)))
println(asize(bders_simp(internalise(TEST), ("a" * 3).toList)))
println(asize(bders_simp(internalise(TEST), ("a" * 4).toList)))
println(asize(bders_simp(internalise(TEST), ("a" * 50000).toList)))

// including decoding
println(blexer_simp(TEST, "a" * 100))
*/

val nreg = STAR(NTIMES(NTIMES("a", 100), 2))
val nstr = "a" * 50000
println(blexer(nreg, nstr))
println(asize(bders_simp(internalise(nreg), nstr.toList)))