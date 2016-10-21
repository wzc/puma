package effect

//read lines from a file
import scala.io.Source

//data structures
import scala.collection.mutable.Map
import scala.collection.mutable.ListBuffer

//match regular expressions
import scala.util.matching.Regex

/**
 * Produce effects for programs in a tiny language.
 *
 * {{{
 * Ins := mov t s | op t s | jmp l s | ret s | inv n s 
 *        with s and t in Reg, l in Lab, and n in Nam
 * prg: Nam -> Reg * (Lab -> Ins)
 * }}}  
 *
 * Big-Step Operational Semantics.
 *
 * {{{
 * S: Nam * Reg -> Val
 *
 * S[(m,t) -> S(m,s)] |- r,m,l+1: _  => S'               S[(m,t) -> h(S(m,s))] |- r,m,l+1: _ => S'           S' = [r -> S(m,s)]
 * ---------------------------------------               -----------------------------------------           -----------------------
 * S |- r,m,l: mov t s => S'                             S |- r,m,l: op t s => S'                            S |- r,m,l: ret s => S' 
 *
 * (x,B) = prg(n)
 * S[(n,x) -> S(m,s)] |- (m,l),n,0: _ => S'              n not in dom(prg)                                   k = h(S(m,s)) ? l' : (l+1)
 * S' |- r,m,l+1: _ => S''                               S |- r,m,l+1: _ => S'                               S |- r,m,k: _ => S'  
 * ---------------------------------------               --------------------------                          --------------------------
 * S |- r,m,l: inv n s => S''                            S |- r,m,l: inv n s => S'                           S |- r,m,l: jmp l' s => S' 
 *
 * (_,B) = prg(m)   l not in dom(B) 
 * --------------------------------                      ------------------
 * S |- r,m,l: _ => S                                    S |- r,m,l: _ => S
 * }}}
 *
 *
 * The Effect System.
 * {{{
 *
 * p in Plc := (m,s) | (?,s) | (?,?)                     with ? unknown
 * e in Exp := ? | !p | h(e)                             with h in Nam
 * w, y in Trc = Nam^*
 *
 * A(p) = {e | e@p in A}                                 with A a relation between Exp and Plc 
 * B[A(p)/!p] = {e[e'/!p]@p'|e@p' in B and e' in A(p)}
 * A ; B = A U B[..,A(p),../..,!p,..]                    simultaneous substitution
 * (w, A) ; (y, B) = (w . y, A ; B)                       
 * A ; {} = A = {} ; A                                   unit 
 * u . w = w  = w . u            
 * (u, {}) ; (w, A) = (w, A) = (w, A) ; (u, {})
 * E ; (E1 U E2) = (E ; E1) U (E ; E2)                   distribution
 * (E1 U E2) ; E = (E1 ; E) U (E2 ; E)
 *
 * E in Eff := {(w, A)} | X_(m,l) | muX_(m,l).E | E1 U E2 | E1 ; E2
 * T in Ctx := {X_(m,l)} | T1 U T2 | {} 
 *
 * T |- r,m,l+1: _ & E                                   T |- r,m,l+1: _ & E
 * E' = {(u, {!(m,s)@(m,t)})} ; E                        E' = {(u, {h(!(m,s))@(m,t)})} ; E                   E = {(u, {!(m,s)@r})}  
 * ------------------------------                        ---------------------------------                   ---------------------
 * T |- r,m,l: mov t s & E'                              T |- r,m,l: op t s & E'                             T |- r,m,l: ret s & E
 *
 * (x, B) = prg(n)                                       
 * T, X_(m,l) |- (m,:l),n,: _ & E1                          
 * T, X_(m,l) |- r,m,l+1: _ & E2                         n not in dom(prg)                                    
 * E1' = {(n, {!(m,s)@(n,x)})} ; E1                      T, X_(m,l) |- r,m,l+1: _ & E2                       E1 = X_(m,l) U {(u, {})}
 * E' = (E1' ; E2) U ({(n, {n(!(m,s))@(m,:l)})} ; E2)    E' = {(n, {n(!(m,s))@(m,:l)})} ; E2                 T, X_(m,l) |- r,m,l+1: _ & E2 
 * E = muX_(m,l).E'                                      E = muX_(m,l).E'                                    E = E1' ; E2'             
 * -------------------------------------------------     ------------------------------------                -------------------------------- 
 * T |- r,m,l: inv n s & E                               T |- r,m,l: inv n s & E                             T, X_(m,l) |- r,m,l: inv n s & E 
 *
 * T, X_(m,l) |- r,m,l': _ & E1
 * T, X_(m,l) |- r,m,l+1: _ & E2 
 * E = muX_(m,l).(E1 U E2)                               E = X_(m,l) U {(u, {})}                             (_,B) = prg(m)   l not in dom(B) 
 * -----------------------------                         ---------------------------------                   --------------------------------
 * T |- r,m,l: jmp l' s & E                              T, X_(m,l) |- r,m,l: jmp l' s & E                   T |- r,m,l: _ & {(u, {})}
 *
 * }}}
 *
 * Example A: loop 
 * {{{
 * 0: jmp 0 x                  E = muX_(?,0).((X_(?,0) U {(,{})}) U {(,{})})
 *                               = {(,{})}
 * }}}            
 *
 * Example B: recursion 
 * {{{
 * 0: inv f s                E1' = {(f,{!(f,x)@(f,x)})} ; (X_(f,0) U {(,{})}) 
 * def f x = 0: inv f x      E2' = {(f,{f(!(f,x))@(f,:0)})}
 *                           E'  = muX_(f,0).(E1' U E2') 
 *                           E   = muX_(?,0).(({(f,{!(?,s)@(f,x)})} ; E') U {(f,{f(!(?,s))@(?,:0)})})
 *                               = {(ff+,{!(?,s)@(f,x), f(!(?,s))@(f,:0)}), (f,{f(!(?,s))@(?,:0)})}
 * }}}
 *
 * Example C: context-sensitive
 * {{{
 * 0: inv f s                  E = {(ff,{{!(?,s),!(?,t)}@(f,x),{!(?,s),f(!(?,s))}@(?,:0),{!(?,t),f(!(?,t))}@(?,:1)})} 
 * 1: inv f t               
 * def f x = 0: ret x      
 * }}}
 *
 * Example D: flow-sensitive
 * {{{
 * 0: jmp 2 s                  E = {(fg, {!(?,s)@(f,x), f(!(?,s))@(?,:1), !(?,s)@(g,x), {!(?,s), g(!(?,s))}@(?,:2)}), 
 * 1: inv f s                       (g,  {!(?,s)@(g,x), {!(?,s), g(!(?,s))}@(?,:2)})}
 * 2: inv g s
 * def f x
 * def g x = 0: ret x
 * }}}
 *
 * Example E: source-to-sink 
 * {{{
 * 0: inv f s                  E = {(fg, {!(?,s)@(f,x), !(?,:0)@(g,x),    g(!(?,:0))@(?,:1), 
 * 1: inv g :0                      f(!(?,s))@(?,:0), f(!(?,s))@(g,x), g(f(!(?,:0)))@(?,:1)})}
 * def f x
 * def g x
 * }}}
 */
class Tiny (prg_file:String) {
  
  type Nam = String
  type Reg = String
  type Lab = String 
  type Plc = String
  type Trc = String
  
  /** Instruction. */
  class Ins (operator:String, target:String, source:String){
    def o = operator
    def t = target
    def s = source
    override def toString = operator + " " + target + " " + source} 

  /** Expression. */
  sealed abstract class Exp
  /** Unkown Value. */
  case class Unk() extends Exp {override def toString = "?"} 
  /** Reference. */
  case class Ref(p:Plc) extends Exp {override def toString = "!" + p} 
  /** Function. */
  case class Fun(m:Nam, e:Exp) extends Exp {override def toString = m + "(" + e + ")"} 
  /** Protected Expression. 
   * @note It is used in simultaneous substitution. */
  case class Prt(e:Exp) extends Exp

  /** Evaluation. */
  sealed abstract class Eva
  /** An expression is evaluated at a place. */
  case class At(e:Exp, p:Plc) extends Eva {override def toString = e + "@" + p} 
 
  /** Effect */
  sealed abstract class Eff 
  /** Atomic Effect. */
  case class Atm(as:List[(Trc, List[Eva])]) extends Eff {
    /** group evaluations by their corresponding traces.*/
    def norm(as:List[(Trc, List[Eva])]): List[(Trc, List[Eva])] =
      if (as == Nil) as
      else as.foldLeft(List(as.head))((x,ea) =>
           if (x.map(eb => ea._1 == eb._1).foldLeft(false)(_ || _)) 
             x.map(eb => if (ea._1 == eb._1) (ea._1, (ea._2 ++ eb._2).distinct) else eb)
           else ea::x)
    var ls:List[(Trc, List[Eva])] = norm(as) 
    /** Expressions evaluated at a place. */
    def exps_at(evas:List[Eva], p:Plc): List[Exp] = 
      evas.map(x => x match {
                      case At(exp, q) =>
                        if (p == q) List(exp)
                        else Nil}).flatten.distinct
    /** Places appearing in evaluations. */
    def plcs(evas:List[Eva]): List[Plc] =
      evas.map(x => x match {case At(_, p) => p}).distinct
    /** Substitute an expression for another in an expression.
     * @note Never do substitution for protected expressions. */
    def sub_exp(exp:Exp, t:Exp, s:Exp): Exp =
      exp match {
        case Unk() => Unk() 
        case Ref(p) => if (s == Ref(p)) Prt(t)
                       else Ref(p)
        case Fun(f,e) => Fun(f, sub_exp(e, t, s))
        case Prt(e) => Prt(e)}
    /** Substitute a set of expressions for an expression in evaluations. */
    def sub_eva(evas:List[Eva], ts:List[Exp], e:Exp): List[Eva] =
      evas.map(eva => 
        ts.map(t => eva match{
                      case At(exp, p) => 
                        At(sub_exp(exp, t, e), p)})).flatten.distinct
    /** Remove protection from an expression.
     * @note After a simultaneous subsitution, the protection is removed. */
    def rm_prt_exp(exp:Exp): Exp =
      exp match {
        case Prt(e) => e
        case Fun(f, e) => Fun(f, rm_prt_exp(e))
        case _ => exp}
    /** Remove protection from evaluations. */
    def rm_prt(evas:List[Eva]): List[Eva] = 
      evas.map(eva => eva match {
                        case At(exp, p) => At(rm_prt_exp(exp),p)})
    /** Concatenation of evaluations */
    def con_evas(as:List[Eva], bs:List[Eva]): List[Eva] =
      (as ++ rm_prt(plcs(as).foldLeft(bs)((x,p) => sub_eva(x, exps_at(as,p), Ref(p))))).distinct
    /** concatenate atomic effects */
    def con(a: Atm): Atm = 
      a match {case Atm(ea) => 
        Atm(ls.map(x => ea.map(y => (x._1 + y._1, con_evas(x._2, y._2)))).flatten)}
    /** union of atomic effects */
    def uni(a: Atm): Atm = 
      a match {case Atm(as) => Atm(ls ++ as)}
    override def toString = {
      var s = "{" 
      for ((w,es) <- ls) {
        s += "(" + w + "," + "{"
        for (e <- es) {s += e + ","}
        if (es.length != 0) s = s.dropRight(1) //remove the extra ","
        s += "}),"} 
      if (ls.length != 0) s = s.dropRight(1) //remove the extra ","
      s += "}"
      s}}
  /** Variable. */
  case class Var(s:String) extends Eff {override def toString = s}
  /** Union. */
  case class Uni(ea:Eff, eb:Eff) extends Eff {override def toString = ea + " + " + eb} 
  /** Concatenation. */
  case class Con(ea:Eff, eb:Eff) extends Eff {override def toString = "[" + ea + " ; " + eb + "]"}


  /** Context for Effect Inference */
  type Ctx = List[Var]

  /** Program */ 
  object prg {
    private val tb = Map[Nam, (Reg, Map[Lab, Ins])]()
    private val eff_tb = Map[Var, Eff]()
    /** Add a definition */
    def insert(m:Nam, a:Reg) : Unit =
      (tb get m) match {
        case Some(_) => 
        case None => tb += (m -> (a, Map[Lab, Ins]()))}
    /** Add an instruction */
    def insert(m:Nam, a:Reg, l:Lab, i:Ins) : Unit =
      (tb get m) match {
        case Some(_) => tb(m)._2 += (l -> i) 
        case None => tb += (m -> (a, Map[Lab, Ins](l -> i)))}
    /** Add an effect equation. */
    def insert_eff(v:Var, e:Eff): Unit =
      eff_tb += (v -> e)

    /** The unit of concatenation of effects */
    val unit = List(("", Nil))  
    
    /** Concatenation of effects. 
     * @note Apply the unit and distribution laws; simplify concatenation of two atomic effects.
     */
    def con(ea:Eff, eb:Eff): Eff = 
      ea match {
        case Atm(as) => 
          if (as == unit) eb //unit law
          else eb match {
            case Atm(bs) =>
              if (bs == unit) ea //unit law
              else Atm(as).con(Atm(bs)) //concatenation of two atoms
            case Uni(ex, ey) => uni(con(ea, ex), con(ea, ey)) //distribution law 
            case _ =>  Con(ea, eb) }
        case Uni(ex, ey) => uni(con(ex, eb), con(ey, eb))
        case _ =>
          eb match {
            case Atm(bs) =>
              if (bs == unit) ea
              else Con(ea,eb)
            case Uni(ex, ey) => uni(con(ea, ex), con(ea, ey))
            case _ => Con(ea,eb)}}
    /** Union of Effects.
     * @note Union of two atomic effects is an atomic effect.
     *       If there is any atomic effect we put it in the first place of a Uni.
     */
    def uni(ea:Eff, eb:Eff): Eff =
      ea match {
        case Atm(as) =>
          eb match {
            case Atm(bs) => Atm(as ++ bs) 
            case Uni(ex, ey) =>
              ex match {
                case Atm(cs) => Uni(Atm(as ++ cs), ey)
                case _ => Uni(ea, eb)} 
            case _ => Uni(ea, eb)}
        case Uni(ex, ey) =>
          eb match {
            case Atm(_) => uni(eb, ea)
            case Uni(ew, ez) =>
              ex match {
                case Atm(xs) =>
                  ew match {
                    case Atm(ws) => Uni(Atm(xs ++ ws), Uni(ey, ez))
                    case _ => Uni(ex, Uni(ey, eb))}
                case _ =>
                  ew match {
                    case Atm(_) => Uni(ew, Uni(ea, ez))
                    case _ => Uni(ea, eb)}}
            case _ => Uni(ex, Uni(ey, eb))}
        case _ =>  
          eb match {
            case Atm(_) => Uni(eb, ea) 
            case Uni(ex, ey) => Uni(ex, Uni(ea, ey))
            case _ => Uni(ea, eb)}}
    
    /** List all variables appearing in an effect */
    def vars(eff:Eff): List[Var] = 
      eff match {
        case Atm(_) => List() 
        case Var(s) => List(Var(s)) 
        case Uni(ea,eb) => vars(ea) ++ vars(eb)  
        case Con(ea,eb) => vars(ea) ++ vars(eb) }

    /** Decide whether a variable refers to itself.
     * @note Have to search the effect table since a variable might be referred indirectly.
     */
    def ref_var(v:Var, eff:Eff): Boolean = {
      var p = ListBuffer[Var]()
      var q = vars(eff).to[ListBuffer].distinct
      while (q != Nil) {
        val a = q(0)
        q -= a
        p += a
        val ns = (eff_tb get a) match {
          case None => ListBuffer()
          case Some(e) => vars(e).to[ListBuffer].distinct }
        q ++= ns.diff(p).diff(q) }
      if (p contains v) true else false }

    /** Least fixed point.
     *
     */
    def lfp(v:Var, eff:Eff): Eff = 
      if (ref_var(v, eff)) {insert_eff(v, eff); v} 
      else eff

    def effect(ctx:Ctx, r:(Nam,Lab), m:Nam, l:Lab) : Eff = {
      val v = Var("X_" + "(" + m + "," + l + ")")
      (tb get m) match {
        case None => Atm(unit)
        case Some((_,blk)) =>  
          (blk get l) match {
            case None => Atm(unit) 
            case Some(ins) =>
              (ins.o) match {
                case "mov" => 
                  val s = ins.s
                  val t = ins.t
                  val E = effect(ctx,r,m,(l.toInt+1).toString) 
                  val e = Atm(List(("",List(At(Ref("("+m+","+s+")"),("("+m+","+t+")"))))))
                  con(e,E)
                case "op" => 
                  val s = ins.s
                  val t = ins.t
                  val E = effect(ctx,r,m,(l.toInt+1).toString) 
                  val e = Atm(List(("",List(At(Fun("h", Ref("("+m+","+s+")")),("("+m+","+t+")"))))))
                  con(e,E)
                case "ret" =>
                  val s = ins.s
                  Atm(List(("",List(At(Ref("("+m+","+s+ ")"),r.toString)))))
                case "jmp" =>
                  var found:Boolean = false 
                  for (x <- ctx)
                    if (x == v) found = true 
                  if (found) {
                    uni(v, Atm(unit)) }
                  else { 
                    val k = ins.t
                    val c = v :: ctx
                    val E1 = effect(c,r,m,k)
                    val E2 = effect(c,r,m,(l.toInt +1).toString)
                    lfp(v, uni(E1, E2)) }
                case "inv" => 
                  var found:Boolean = false
                  for (x <- ctx)
                    if (x == v) found = true 
                  if (found) { 
                    val e = uni(v, Atm(unit))
                    val E = effect(ctx,r,m,(l.toInt +1).toString)
                    con(e,E) }
                  else {
                    val c = v :: ctx
                    val n = ins.t
                    val s = ins.s
                    val E2 = effect(c,r,m,(l.toInt +1).toString)
                    val E22 = con(Atm(List((n,List(At(Fun(n,Ref("("+m+","+s+")")),("("+m+",:"+l+")")))))), E2)
                    (tb get n) match {
                      case None => lfp(v, E22)
                      case Some((x,_)) =>
                        val E1 = effect(c,(m,":"+l),n,"0")
                        val E11 = con(Atm(List((n,List(At(Ref("("+m+","+s+")"),("("+n+","+x+")")))))), E1)
                        val E = uni(con(E11, E2), E22)
                        lfp(v, E)}}
                case _ => Atm(unit) }}}} 

    def print: Unit =
      for (nam <- tb.keys) {
        var (arg, blk) = tb(nam)
        println(nam + " " + arg)
        blk.keys.foreach(lab => println(lab.toString + ": " + blk(lab)))}
    def print_eff: Unit =
      eff_tb.keys.foreach(x => println(x + ": " + eff_tb(x)))
  } 

  type Pattern = Regex 
  type Tag = String
  
  private val REG:Pattern = ("[a-z0-9:,?]+").r
  private val LAB:Pattern = ("[0-9]+").r
  private val NAM:Pattern = ("[a-z0-9]+").r

  private val MOV:Pattern = ("([0-9]+): mov (" + REG.toString + ") (" + REG.toString + ")").r
  private val OP:Pattern = ("([0-9]+): op (" + REG.toString + ") (" + REG.toString + ")").r
  private val JMP:Pattern = ("([0-9]+): jmp (" + LAB.toString + ") (" + REG.toString + ")").r
  private val INV:Pattern = ("([0-9]+): inv (" + NAM.toString + ") (" + REG.toString + ")").r
  private val RET:Pattern = ("([0-9]+): ret (" + REG.toString + ")").r
  private val DEF:Pattern = ("def ([a-z]+) ([a-z]+)").r

  private val patTag = Map[Pattern, Tag]()
  patTag += (MOV -> "mov")
  patTag += (OP -> "op")
  patTag += (JMP -> "jmp")
  patTag += (INV -> "inv")
  patTag += (RET -> "ret")
  patTag += (DEF -> "def")
 
  private var nam:Nam = "?"
  private var arg:Reg = "?"

  def decode_line(line:String) : Unit = 
    for (pat <- patTag.keys)
      pat.findFirstIn(line) match {
        case None =>
        case Some(_) =>
          patTag(pat) match {
            case "def" => 
              val pat(n, a) = line; nam = n; arg = a; prg.insert(nam, arg)
            case "ret" =>
              val pat(lab, s) = line; prg.insert(nam, arg, lab, new Ins("ret", "", s))
            case _ => 
              val pat(lab, t, s) = line
              prg.insert(nam, arg, lab, new Ins(patTag(pat), t, s))}}

  for (line <- Source.fromFile(prg_file).getLines()) {
    decode_line(line)}

  prg.print
  println(prg.effect(Nil,("?","?"),"?","0"))
  prg.print_eff
}
