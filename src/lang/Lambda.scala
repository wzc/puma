package lang 

/**
 * Translate code in LightAndroid into enriched Lambda expressions.
 * 
 * {{{
 * xs: all registers used in a method. 
 * +---------------------------------------------------------------------+
 * |  (l, mov t s)      -> (l, \xs.(let t = s in l+1 xs))                | 
 * |  (l, const t a)    -> (l, \xs.(let t = a in l+1 xs))                | 
 * |  (l, iget t s.f)   -> (l, \xs.(let t = s.f in l+1 xs))              | 
 * |  (l, iput t.f s)   -> (l, \xs.(let t.f = s in l+1 xs))              | 
 * |  (l, sget t C.f)   -> (l, \xs.(let t = C.f in l+1 xs))              | 
 * |  (l, sput C.f s)   -> (l, \xs.(let C.f = s in l+1 xs))              | 
 * +---------------------------------------------------------------------+
 * |  (l, op)           -> (l, \xs.(l+1 xs))                             | 
 * |  (l, op t s)       -> (l, \xs.(let t = 'op s in l+1 xs))            | 
 * |  (l, op t s s')    -> (l, \xs.(let t = 'op s s' in l+1 xs))         | 
 * |  (l, op t s a)     -> (l, \xs.(let t = 'op s a in l+1 xs))          | 
 * |  (l, op t s C)     -> (l, \xs.(let t = 'op s C in l+1 xs))          | 
 * +---------------------------------------------------------------------+
 * |  (l, jmp l')       -> (l, \xs.(l' xs))                              | 
 * |  (l, jmp l' s)     -> (l, \xs.(cond('op s, l' xs, l+1 xs))          | 
 * |  (l, jmp l' s s')  -> (l, \xs.(cond('op s s', l' xs, l+1 xs))       |
 * |  (l, jmp ls s)     -> (l, \xs.(cond('op s, ls[0] xs, ..., ls[n] xs))| 
 * +---------------------------------------------------------------------+
 * |  (l, inv r C.m:T args) -> (l, \xs.(let r = C.m:T args in l+1 xs))   | 
 * +---------------------------------------------------------------------+
 * |  (l, ret)          -> (l, \xs.())                                   | 
 * |  (l, ret s)        -> (l, \xs.s)                                    | 
 * +---------------------------------------------------------------------+
 * |  (l, new t C)      -> (l, \xs.(let t - unit in l+1 xs))             | 
 * |  (l, new t n)      -> (l, \xs.(let t = unit in l+1 xs))             | 
 * |  (l, new t #as as) -> (l, \xs.(let t.0 = as[0] in                   |
 * |                                let t.1 = as[1] in                   |
 * |                                ...                                  |
 * |                                let t.n = as[n] in l+1 xs))          | 
 * +---------------------------------------------------------------------+
 * }}}
 *
 * @author Wei Chen, Harmony Singh @ University of Edinburgh, 01/07/2017 - 31/07/2017 
 */

class Lambda(_la:LightAndroid) {

  def la:LightAndroid = _la

  /** Expression. 
   * Exp ::= Const | Var | Fld | Fun [Exp] | Op [Exp] | Lab | Abs [Var] Exp | App Exp Exp | Let Exp Exp Exp | Cond [Exp] 
   */

  sealed abstract class Exp
    case class Const (s:String) extends Exp {override def toString = s} 
    case class Var (s:String) extends Exp {override def toString = s} 
    case class Nam (s:String) extends Exp {override def toString = s} 
    case class Cls (s:String) extends Exp {override def toString = s} 
    case class SFld (cls:Cls, f:Nam) extends Exp {override def toString = cls + "." + f} 
    case class IFld (v:Var, f:Nam) extends Exp {override def toString = v + "." + f} 
    case class Typ (s:String) extends Exp {override def toString = s} 
    case class Fun (cls:Cls, name:Nam, typ:Typ) extends Exp {override def toString = cls + "." + name + ":" + typ} 
    case class Op (xs:List[Exp]) extends Exp {override def toString = "op" + xs.map(x => x.toString).foldLeft("")(_+ " " +_)} 
    case class Lab (i:Int) extends Exp {override def toString = i.toString} 
    case class Abs (xs:List[Exp], e:Exp) extends Exp {override def toString = "\\" + xs.map(x => x.toString).foldLeft("")(_+ " " +_) + " . " + e} 
    case class App (ea:Exp, xs:List[Exp]) extends Exp {override def toString = ea + xs.map(x => x.toString).foldLeft("")(_+ " " +_)} 
    case class Let (ea:Exp, eb:Exp, ec:Exp) extends Exp {override def toString = "let " + ea + " = " + eb + " in " + ec} 
    case class Cond (c:Exp, es:List[Exp]) extends Exp {override def toString = "cond(" + c  + es.map(x => x.toString).foldLeft("")(_+ ", " +_) + ")"}
    case class Unit () extends Exp {override def toString = "unit"}
    case class Star () extends Exp {override def toString = "*"}
    case class Fix (e:Exp) extends Exp {override def toString = "fix(\\ " + e + ")"} 

  type Label = String
 
  def subst(e:Exp, t:Exp, s:Exp) : Exp = {
    val f = (l:List[Exp]) => l.map(x => subst(x,t,s))
    if (e == s) t 
    else e match {
           case Abs(xs,ea) => Abs(f(xs), subst(ea,t,s)) 
           case App(ea,xs) => App(subst(ea,t,s), f(xs))
           case Cond(ea,xs) => Cond(subst(ea,t,s), f(xs))
           case Fix(ea) => Fix(subst(ea,t,s))
           case _ => e
         } 
  } 

  def elim(xs:List[Exp], es:List[(Label,Exp)]) : Exp = {
    es match {
      case Nil => Abs(xs, Unit())
      case (l,t) :: ts => val ls = ref(t) 
                          if (ls == Nil && ts == Nil) t
                          else if (ls.contains(l)) elim(xs, ts ++ List((l, Fix(subst(t, Star(), Lab(l.toInt)))))) 
                               else if (l != "0") elim(xs, ts.map(lt => (lt._1, subst(lt._2, t, Lab(l.toInt)))))
                                    else elim(xs, ts ++ List((l,t)))
    }
  }

  /** A recursive function to extract labels from an expression 
  * Takes an expression as a parameter. 
  */

  def ref(e:Exp) : List[Label] = {
    val f = (l:List[Exp]) => l.foldRight(List[Label]())((x,y) => ref(x) ++ y)
    e match {
      case Lab(i) => List(i.toString)
      case Abs(es, eb) => f(es ++ List(eb))
      case App(ea, es) => f(List(ea) ++ es)
      case Let(ea, eb, ec) => f(List(ea,eb,ec))
      case Cond(ea, es) => f(ea :: es)
      case Fix(e) => f(List(e))
      case _ => Nil 
    }
  }

  //Converts instructions to Lambda expressions, returns a tuple containing a label and an Exp
  def ins2exp(l:Label, ins:Ins, xs:List[Exp]) : (Label, Exp) = {
    ins.op match {
      case "jmp" => if (ins.src.length == 0) // unconditional jump 
                      (l, Abs(xs, Cond(Star(), ins.ta.map(x => App(Lab(x.toInt), xs)))))
                    else if (ins.ta.length == 1) // conditional jump 
                      (l, Abs(xs, Cond(Op(ins.src.map(x => Var(x))), 
                                          App(Lab(l.toInt + 1), xs) :: ins.ta.map(x => App(Lab(x.toInt), xs))) ))  
                    else // switches
                      (l, Abs(xs, Cond(Op(ins.src.map(x => Var(x))), 
                                          ins.ta.map(x => App(Lab(x.toInt), xs)))))  

      case "op" => if (ins.ta.isEmpty && ins.src.isEmpty) // no operands
                     (l, Abs(xs, App(Lab(l.toInt + 1), xs))) 
                   else // more than one operand, assuming the target list contains only one variable
                     (l, Abs(xs, Let(Var(ins.ta.head), Op(ins.src.map(x => Var(x))), App(Lab(l.toInt + 1), xs))))

      case "ret" => if (ins.src.isEmpty) // returns nothing
                      (l, Abs(xs, Unit()))
                    else // assuming the source list contains only one variable
                      (l, Abs(xs, Var(ins.src.head)))
                      
      case "inv" => val s = ins.src // tar = [def_reg = "v"], src = [cls, name, typ] ++ args
                    val t = s.tail.tail.tail
                    (l, Abs(xs, Let(Var(ins.ta.head), 
                                    App(Fun(Cls(s(0)), Nam(s(1)), Typ(s(2))), t.map(x => Var(x))), 
                                    App(Lab(l.toInt + 1), xs))))

      case "mov" => (l, Abs(xs, Let(Var(ins.ta.head), 
                                    Var(ins.src.head),
                                    App(Lab(l.toInt + 1), xs))))
      case "const" => (l, Abs(xs, Let(Var(ins.ta.head), 
                                      Const(ins.src.head),
                                      App(Lab(l.toInt + 1), xs))))
      case "iget" => (l, Abs(xs, Let(Var(ins.ta.head), 
                                     IFld(Var(ins.src(0)), Nam(ins.src(1))),
                                     App(Lab(l.toInt + 1), xs))))
      case "iput" => (l, Abs(xs, Let(IFld(Var(ins.ta(0)), Nam(ins.ta(1))),
                                     Var(ins.src.head), 
                                     App(Lab(l.toInt + 1), xs))))
      case "aget" => (l, Abs(xs, Let(Var(ins.ta.head), 
                                     IFld(Var(ins.src(0)), Nam(ins.src(1))),
                                     App(Lab(l.toInt + 1), xs))))
      case "aput" => (l, Abs(xs, Let(IFld(Var(ins.ta(0)), Nam(ins.ta(1))),
                                     Var(ins.src.head), 
                                     App(Lab(l.toInt + 1), xs))))
      case "sget" => (l, Abs(xs, Let(Var(ins.ta.head), 
                                     SFld(Cls(ins.src(0)), Nam(ins.src(1))),
                                     App(Lab(l.toInt + 1), xs))))
      case "sput" => (l, Abs(xs, Let(SFld(Cls(ins.ta(0)), Nam(ins.ta(1))),
                                     Var(ins.src.head), 
                                     App(Lab(l.toInt + 1), xs))))
      case "new" => if (ins.src.length == 1) // new t C or new t n 
                      (l, Abs(xs, Let(Var(ins.ta.head),
                                      Unit(), 
                                      App(Lab(l.toInt + 1), xs))))
                    else{ // new t #ns ns
                      val t = ins.ta.head
                      val ns = ins.src.tail
                      val fin:Exp = App(Lab(l.toInt + 1), xs)
                      val f = (x:String, y:Exp) => Let(IFld(Var(t), Nam(ns.indexOf(x).toString)), Const(x), y)
                      (l, ns.foldRight(fin)(f)) } 
      
      case _ => (l, Unit())
    }
  }
    
  //val bd = la.method.body("Landroid/support/graphics/drawable/AnimatedVectorDrawableCompat$AnimatedVectorDrawableDelegateState;", 
  //                        "newDrawable",
  //                        "(Landroid/content/res/Resources;)Landroid/graphics/drawable/Drawable;")

  val bd = la.method.body("Lcom/app/demo/R$styleable;",
                          "<clinit>",
                          "()V")
  
  //val bd = la.method.body("Lcom/app/demo/MainActivity;", "gcd", "(II)V")

  val args = la.method.args("Lcom/app/demo/MainActivity;", "gcd", "(II)V") match {
  	case Some(lst) => lst.map(x=> Var(x)) //adding all aruguments to a list
  	case None => List()
  }
  
  val xs = 
    la.method.regs("Lcom/app/demo/MainActivity;", "gcd", "(II)V") match {
      case Some(lst) => lst.map(x => Var(x)) //adding all registers to a list
      case None => List() 
    }
  
  bd match {
    case Some(lst) => println(elim(xs, lst.map(x => ins2exp(x._1,x._2,xs))))
    case None => 
  }
}
