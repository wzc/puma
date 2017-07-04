package lang 

/**
 * Translate code in LightAndroid into enriched Lambda expressions.
 * 
 * {{{
 * xs: all registers used in a method. 
 * +---------------------------------------------------------------------+
 * |  (l, mov t s)      -> (l, \xs.(let t = s in l+1 xs))                | 
 * |  (l, mov t a)      -> (l, \xs.(let t = a in l+1 xs))                | 
 * |  (l, mov t s.f)    -> (l, \xs.(let t = s.f in l+1 xs))              | 
 * |  (l, mov t.f s)    -> (l, \xs.(let t.f = s in l+1 xs))              | 
 * |  (l, mov t C.f)    -> (l, \xs.(let t = C.f in l+1 xs))              | 
 * |  (l, mov C.f s)    -> (l, \xs.(let C.f = s in l+1 xs))              | 
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
 * |  (l, new t C)      -> (l, \xs.(l+1 xs))                             | 
 * |  (l, new t n)      -> (l, \xs.(l+1 xs))                             | 
 * |  (l, new t #as as) -> (l, \xs.(let t = as in l+1 xs))               | 
 * +---------------------------------------------------------------------+
 * }}}
 *
 * @author Wei Chen, Harmony Signh @ University of Edinburgh, 01/07/2017 - 07/07/2017 
 */

class Lambda() {  

  /** Expression. 
   * Exp ::= Const | Var | Fld | Fun [Exp] | Op [Exp] | Lab | Abs [Var] Exp | App Exp Exp | Let Exp Exp Exp | Cond [Exp] 
   */
  /*---------------------------------------------------------------------------------------------------------------------------------------------------------*/
  sealed abstract class Exp
    case class Const (s:String) extends Exp {override def toString = s} 
    case class Var (s:String) extends Exp {override def toString = s} 
    case class Fld (s:String, f:String) extends Exp {override def toString = s + "." + f} 
    case class Fun (s:String, xs:List[Exp]) extends Exp {override def toString = s + " " + xs.map(x => x.toString).reduceLeft(_+ " " +_)} 
    case class Op (xs:List[Exp]) extends Exp {override def toString = "op " + xs.map(x => x.toString).reduceLeft(_+ " " +_)} 
    case class Lab (i:Int) extends Exp {override def toString = i.toString} 
    case class Abs (xs:List[Exp], e:Exp) extends Exp {override def toString = "\\" + xs.map(x => x.toString).reduceLeft(_+ " " +_) + "." + e} 
    case class App (ea:Exp, eb:Exp) extends Exp {override def toString = ea + " " + eb} 
    case class Let (ea:Exp, eb:Exp, ec:Exp) extends Exp {override def toString = "let " + ea + " = " + eb + " in " + ec} 
    case class Cond (c:Exp, es:List[Exp]) extends Exp {override def toString = "cond(" + c + es.map(x => x.toString).reduceLeft(_+ " " +_) + ")"} 
  /*--End-of-Expression--------------------------------------------------------------------------------------------------------------------------------------*/
  val x = Let (Var ("y"), Op (List(Var ("x"), Var ("y"))), Const ("unit")) 
  println(x)
}
