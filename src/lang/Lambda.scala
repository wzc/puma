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
  sealed abstract class Exp
    case class Var (var s:String) extends Exp {override def toString = s} 
    case class App (var ea:Exp, var eb:Exp) extends Exp {override def toString = ea + " " + eb}
    case class Abs (var xs:List[Var], var e:Exp) extends Exp {override def toString = "\\" + xs + "." + e}
    case class Let (var x:Var, var ea:Exp, var eb:Exp) extends Exp {override def toString = "let " + x + " = " + ea + " in " + eb} 
  val x = Let (Var("x"), Var("op b c"), App (Var("d"), Var ("x")))
  println(x)
}
