
/*
 * 制約充足問題 (Constraint Satisfaction Problem; CSP) に関するクラスを定義するためのファイル
 */
/* cspを構成する要素のスーパークラス*/
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
}

case class CSP(
                var vars: Seq[Variable],
                var doms: Map[Variable, Domain],
                var cons: Seq[Constraint]
              ){
  def hasNoEmptyDomain = doms.forall(_._2.size > 0)
  def isSatisfiedWith(a: Assignment) = cons.forall(_.isSatisfiedWith(a))

  lazy val var2cons = (for (x <- vars) yield x -> cons.filter(_.vars.contains(x))).toMap

  def toSugar(t: Expression): String = t match {
    case x: Variable => s"(int ${x.name} ${toSugar(doms(x))})"
    case d: Domain => if (d.values.size == d.ub - d.lb + 1) s"${d.lb} ${d.ub}" else d.values.mkString(" ")
    case Ne(x1: Variable, x2: Variable) => s"(ne ${x1.name} ${x2.name})"
    case Alldifferent(x1: Variable, x2: Variable, x3: Variable) => s"(alldifferent ${x1.name} ${x2.name}  ${x3.name})"
  }


  def toSugar: Seq[String] = {
    vars.map(toSugar(_)) ++ cons.map(toSugar(_))
  }
}

object CSP {
  def apply() = new CSP(Seq.empty,Map.empty,Seq.empty)
}

case class Assignment(amap: Map[Variable, Int]){
  def apply(x: Variable) = amap(x)

  def contains(x: Variable) = amap.contains(x)

  def +(x: Variable, v: Int) = Assignment(amap + (x -> v))

  def +(xv: Tuple2[Variable, Int]) = Assignment(amap + (xv._1 -> xv._2))

  def toDoms: Map[Variable, Domain] = amap.map { xv => xv._1 -> Domain(Seq(xv._2)) }

  override def toString = {
    amap.map{case (x, v) => s"v ${x.name} = $v"}.mkString("\n")
  }
}

object Assignment{
  def apply(): Assignment = Assignment(Map.empty)
}
//case class Add(ts:Seq[Term]) extends Term {

//}


case class Ne(x1: Term, x2: Term) extends Constraint {
  def vars = x1.vars ++ x2.vars
  def isSatisfiedWith(a: Assignment) = x1.valuedWith(a) != x2.valuedWith(a)
}

case class Alldifferent(x1: Term, x2: Term, x3: Term) extends Constraint {
  def vars = x1.vars ++ x2.vars ++ x3.vars
  def isSatisfiedWith(a: Assignment) = {
    x1.valuedWith(a) != x2.valuedWith(a)
    x2.valuedWith(a) != x3.valuedWith(a)
    x1.valuedWith(a) != x3.valuedWith(a)
  }
}
//case class Ne(x1: Variable, x2: Variable) extends Constraint {
//  def vars = Set(x1, x2)
//  def isSatisfiedWith(a: Assignment) = a(x1) != a(x2)
//}

object cspFactory {
  private[this] def varFactory(x: SIntVar): Variable = Variable(x.name)
  private[this] def domFactory(d: SDomain) = {
    val ds = d.dom.foldLeft(Seq.empty[Int])((seq, lu) => seq ++ (lu._1 to lu._2))
    Domain(ds)
  }
  private[this] def termFactory(t: SugarCspTerm): Term = {
    t match {
      case x: SIntVar => varFactory(x)
      //case t: SAdd => Add(t.ts.map(termFactory()))
      //case _ =>
    }
  }
  private[this] def constraintFactory(c: SugarCspConstraint): Constraint = {
    c match {
      case SNe(t1: SIntVar, t2: SIntVar) => Ne(varFactory(t1), varFactory(t2))
      case Alldifferent(t1: SIntVar, t2: SIntVar) => Alldifferent(varFactory(t1), varFactory(t2))
      case t: SGe => ???
      case d: SAdd => ???
      case f: SEq => ???
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


/*
  (ne x1 x2)
  (ne x1 1)
  (eq x1 x2)
* */
