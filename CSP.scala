
/*
 * 制約充足問題 (Constraint Satisfaction Problem; CSP) に関するクラスを定義するためのファイル
 */

abstract class Expression

abstract class Term extends Expression {
  def vars: Set[Variable]
  def valuedWith(a: Assignment): Int
}

case class Variable(name: String) extends Term {
  def vars = Set(this)
  def valuedWith(a: Assignment) = a(this)
}

case class Domain(values: Seq[Int]) extends Expression {
  def lb = values.min
  def ub = values.max
  def size = values.size
}

abstract class Constraint extends Expression {
  def vars: Set[Variable]
  def isSatisfiedWith(a: Assignment): Boolean
  def &&(c: Constraint) = And(Seq(this,c))
  //def &&(cs: Seq[Constraint]) = And(cs)
  def ||(cs: Seq[Constraint]) = Or(cs)
}

abstract class LogicalFormula extends  Constraint {
  def vars: Set[Variable]
  def isSatisfiedWith(a: Assignment): Boolean
}

case class CSP(
                var vars: Seq[Variable],
                var doms: Map[Variable, Domain],
                var cons: Seq[Constraint]
              )  {

  def hasNoEmptyDomain = doms.forall(_._2.size > 0)
  def isSatisfiedWith(a: Assignment) = cons.forall(_.isSatisfiedWith(a))

  lazy val var2cons = (for (x <- vars) yield x -> cons.filter(_.vars.contains(x))).toMap

  def toSugar(t: Expression): String = t match {
    case x: Variable => s"(int ${x.name} ${toSugar(doms(x))})"
    case d: Domain => if (d.values.size == d.ub - d.lb + 1) s"${d.lb} ${d.ub}" else d.values.mkString(" ")
    case Ne(x1: Term, x2: Term) => s"(ne $x1 $x2)"
    case Eq(x1: Term, x2: Term) => s"(eq $x2 $x2)"
  }

  def toSugar: Seq[String] = {
    vars.map(toSugar(_)) ++ cons.map(toSugar(_))
  }
}

object CSP {
  def apply() = new CSP(Seq.empty, Map.empty, Seq.empty)
}

case class Assignment(amap: Map[Variable, Int]) {
  def apply(x: Variable) = amap(x)

  def contains(x: Variable) = amap.contains(x)

  def +(x: Variable, v: Int) = Assignment(amap + (x -> v))

  def +(xv: Tuple2[Variable, Int]) = Assignment(amap + (xv._1 -> xv._2))

  def toDoms: Map[Variable, Domain] = amap.map { xv => xv._1 -> Domain(Seq(xv._2)) }

  override def toString = {
    amap.map{case (x, v) => s" ${x.name} = $v"}.mkString("\n")
  }
}

object Assignment {
  def apply(): Assignment = Assignment(Map.empty)
}


/** Term type which has many Terms */
abstract class seqTermsOfTerm(ts: Seq[Term]) extends Term {
    var Ts: Set[Variable] = Set()
    for (t <- ts) Ts = Ts ++ t.vars
    def vars: Set[Variable] = Ts
}
case class Add(ts: Seq[Term]) extends seqTermsOfTerm(ts: Seq[Term]) {
  def valuedWith(a: Assignment): Int = {
    var Ts = 0
    for (t <- ts) Ts += t.valuedWith(a)
    Ts
  }
}
case class Min(ts: Seq[Term]) extends seqTermsOfTerm(ts: Seq[Term]) {
  def valuedWith(a: Assignment): Int = {
    var minTs = Int.MaxValue
    for (t <- ts) if (minTs > t.valuedWith(a)) minTs = t.valuedWith(a)
    minTs
  }
}
case class Max(ts: Seq[Term]) extends seqTermsOfTerm(ts: Seq[Term]) {
  def valuedWith(a: Assignment): Int = {
    var maxTs = Int.MinValue
    for (t <- ts) if (maxTs < t.valuedWith(a)) maxTs = t.valuedWith(a)
    maxTs
  }
}

/** Term type which has two Terms */
abstract class twoTermsOfTerm(t1: Term, t2: Term) extends Term{
   def vars: Set[Variable] = t1.vars ++ t2.vars
}
case class Mod(t1: Term, t2: Term) extends twoTermsOfTerm(t1: Term, t2: Term)  {
  override def valuedWith(a: Assignment): Int = t1.valuedWith(a) % t2.valuedWith(a)
}
case class Mul(t1: Term, t2: Term) extends twoTermsOfTerm(t1: Term, t2: Term)  {
  override def valuedWith(a: Assignment): Int = t1.valuedWith(a) * t2.valuedWith(a)
}
case class Pow(t1: Term, t2: Term) extends twoTermsOfTerm(t1: Term, t2: Term)  {
  override def valuedWith(a: Assignment): Int = Math.pow(t1.valuedWith(a), t2.valuedWith(a)).toInt
}
case class Div(t1: Term, t2: Term) extends twoTermsOfTerm(t1: Term, t2: Term)  {
  override def valuedWith(a: Assignment): Int = t1.valuedWith(a) / t2.valuedWith(a)
}

/**Other Term types */
case class Sub(t1: Term, ts:Seq[Term]) extends Term {
  var Ts: Set[Variable] = Set()
  for (t <- ts) Ts = Ts ++ t.vars
  def vars: Set[Variable] = Ts
  def valuedWith(a: Assignment): Int = {
    var sumTs = 0
    for (t <- ts) sumTs += t.valuedWith(a)
    t1.valuedWith(a) - sumTs
  }
}
case class Num(n: Int) extends Term {
  override def vars: Set[Variable] = Set()
  override def valuedWith(a: Assignment): Int = n
}

/** Constraint type which has many terms */
abstract class seqConstraint(cs: Seq[Constraint]) extends Constraint{
  var Ts: Set[Variable] = Set()
  for (t <- cs) Ts = Ts ++ t.vars
  def vars: Set[Variable] = Ts
 }
case class Or(cs: Seq[Constraint]) extends  seqConstraint(cs: Seq[Constraint]){
   def isSatisfiedWith(a: Assignment): Boolean = cs.exists(_.isSatisfiedWith(a))
}
case class And(cs: Seq[Constraint]) extends seqConstraint(cs: Seq[Constraint]) {
   def isSatisfiedWith(a: Assignment): Boolean = cs.forall(_.isSatisfiedWith(a))
}


/** Constraint type which has two terms */
abstract class twoTermsConstraint(t1: Term, t2: Term) extends Constraint {
   def vars: Set[Variable] = t1.vars ++ t2.vars
}
case class Ne(t1: Term, t2: Term) extends twoTermsConstraint(t1: Term, t2: Term) {
   def isSatisfiedWith(a: Assignment): Boolean = t1.valuedWith(a) != t2.valuedWith(a)
}

case class Eq(t1: Term, t2: Term) extends twoTermsConstraint(t1: Term, t2: Term) {
   def isSatisfiedWith(a: Assignment): Boolean = t1.valuedWith(a) == t2.valuedWith(a)
}

case class Ge(t1: Term, t2: Term) extends twoTermsConstraint(t1: Term, t2: Term) {
   def isSatisfiedWith(a: Assignment): Boolean = t1.valuedWith(a) >= t2.valuedWith(a)
}


/** Alldifferent class of Constraints  */
case class AllDifferent(ts: Seq[Term]) extends Constraint {
  var Ts: Set[Variable] = Set()
  for (t <- ts) Ts = Ts ++ t.vars
  def vars: Set[Variable] = Ts
  def isSatisfiedWith(a: Assignment): Boolean = {
    for (i <- ts.indices;j <- i+1 until ts.size if ts(i).valuedWith(a) == ts(j).valuedWith(a)) return false
    true
  }
}

/** CspFactory method */
object cspFactory {
  private[this] def varFactory(x: SIntVar): Variable = Variable(x.name)
  private[this] def domFactory(d: SDomain) = {
    val ds = d.dom.foldLeft(Seq.empty[Int])((seq, lu) => seq ++ (lu._1 to lu._2))
    Domain(ds)
  }
  private[this] def termFactory(t: SugarCspTerm): Term = {
    t match {
      case n: SNum => Num(n.n)
      case x: SIntVar => varFactory(x)
      case SAdd(ts: Seq[SugarCspTerm]) => Add(ts.map(termFactory(_)))
      case SSub(ts: Seq[SugarCspTerm]) => Sub(termFactory(ts.head), ts.tail.map(termFactory(_)))
      case SMul(t1: SugarCspTerm, t2:SugarCspTerm) => Mul(termFactory(t1), termFactory(t2))
      case SDiv(t1: SugarCspTerm, t2:SugarCspTerm) => Div(termFactory(t1), termFactory(t2))
      case SMod(t1: SugarCspTerm, t2:SugarCspTerm) => Mod(termFactory(t1), termFactory(t2))
      case SPow(t1: SugarCspTerm, t2:SugarCspTerm) => Pow(termFactory(t1), termFactory(t2))
      case SMin(ts: Seq[SugarCspTerm]) => Min(ts.map(termFactory(_)))
      case SMax(ts: Seq[SugarCspTerm]) => Max(ts.map(termFactory(_)))
    }
  }
  private[this] def constraintFactory(c: SugarCspConstraint): Constraint = {
    c match {
      case SAnd(cs: Seq[SugarCspConstraint]) => And(cs.map(constraintFactory(_)))
      case SOr(cs: Seq[SugarCspConstraint]) => Or(cs.map(constraintFactory(_)))
      case SEq(t1: SugarCspTerm, t2: SugarCspTerm) => Eq(termFactory(t1), termFactory(t2))
      case SNe(t1: SugarCspTerm, t2: SugarCspTerm) => Ne(termFactory(t1), termFactory(t2))
      case SGe(t1: SugarCspTerm, t2: SugarCspTerm) => Ge(termFactory(t1), termFactory(t2))
      case SAllDifferent(ts: Seq[SugarCspTerm]) => AllDifferent(ts.map(termFactory(_)))
    }
  }
  def fromFile(fileName: String): CSP = {
    val csp = CSP()
    val sp = new SugarCspLangParser
    sp.parse(new java.io.File(fileName))
    sp.domMap.keys.foreach { x0 =>
      val x = varFactory(x0)
      csp.vars = x +: csp.vars
      csp.doms += x -> domFactory(sp.domMap(x0))
    }
    csp.cons = sp.scons.map(constraintFactory)
    csp
  }
}
