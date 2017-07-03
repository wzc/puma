package lang

// read lines from a file
import scala.io.Source

// data structures
import scala.collection.mutable.Map

// match regular expressions
import scala.util.matching.Regex

// seek a position in a file
import java.io.RandomAccessFile

// execute system commands
import scala.sys.process._ 
 
/**
 * Convert Android apps in Dalvik code into programs in the abstract analysis language: light Android.
 * 
 * This translation simplifies code by reducing more than 200 Dalvik opcodes into 6 abstract instructions.
 *
 * It preserves semantics for further behavioural analysis of Android apps.  
 *
 * The map from Dalvik opcodes to abstract instructions in light Android is as follows.
 *
 *
 * {{{ 
 * +--------------------------------------------------+-------------------------------------------------------------------+
 * |  move t s                  -> mov t s            |  nop, monitor s,                                                  | 
 * |  const t a                 -> mov t a            |  move-exception t,                                                |
 * |  iget t s f, aget t s f    -> mov t s.f          |  check-cast s C                 -> op                             | 
 * +--------------------------------------------------+-------------------------------------------------------------------+
 * |  iput s t f, aput s t f    -> mov t.f s          |  neg t s, not t s, *-to-* t s,                                    |
 * |  sget t C f                -> mov t C.f          |  array-length t s               -> op t s                         | 
 * +--------------------------------------------------+-------------------------------------------------------------------+
 * |  sput s C f                -> mov C.f s          |  cmp, add, sub, rsub, mul,                                        | 
 * |  new-instance t C          -> new t C            |  div, rem, and, or, xor, shl,                                     |
 * |  new-array t n C           -> new t n            |  shr, ushr, instance-of t s C   -> op t s s', op t s a, op t s C  |
 * +--------------------------------------------------+-------------------------------------------------------------------+
 * |  filled-new-array as C     -> new t #as as       |  goto l                         -> jmp l                          |
 * +--------------------------------------------------+-------------------------------------------------------------------+
 * |  fill-array t l               jmp l              |  if-* s l                       -> jmp l s                        | 
 * |  l: array-data #as as      -> new t #as as       |  if-* s s' l                    -> jmp l s s'                     |
 * +--------------------------------------------------+-------------------------------------------------------------------+
 * |  l: invoke args C m T      -> inv r C.m:T args   |  *-switch s l                      jmp l                          |
 * |  l+1: move-result t        -> mov t r            |  l: *-switch-data keys ls       -> jmp ls s                       |
 * +--------------------------------------------------+-------------------------------------------------------------------+
 * |  return-void, throw e      -> ret                |  return s                       -> ret s                          |
 * +--------------------------------------------------+-------------------------------------------------------------------+
 * }}}
 *
 *
 * @example
 * {{{
 * val la = new LightAndroid("./exp/classes.dex", "./exp/dex_dump.txt")
 * }}}
 * creates an instance of LightAndroid from the .dex file "classes.dex" and "dex_dump.txt" which is output of the command "dexdump -d classes.dex".
 * {{{
 * la.superclass.get("Lcom/app/demo/MainActivity;")
 * la.interface.get("Lcom/app/demo/MainActivity;")
 * la.static_field.get("Lcom/app/demo/MainActivity;")
 * la.instance_field.get("Lcom/app/demo/MainActivity;")
 * }}}
 * get the superclass, interfaces and fields of the class "Lcom/app/demo/MainActivity;".
 *
 * {{{
 * la.method.get("Lcom/app/demo/MainActivity;", "gcd", "(II)V")
 * la.method.args("Lcom/app/demo/MainActivity;", "gcd", "(II)V")
 * la.method.body("Lcom/app/demo/MainActivity;", "gcd", "(II)V")
 * }}}
 * get the definition (arguments, body), formal arguments and body of the method "gcd".
 *
 * @author Wei Chen @ University of Edinburgh, 25/06/2016 - 27/07/2016, 01/07/2017 
 * 
 */
class LightAndroid (classes_dex_file:String, dex_dump_file:String) {

  /**
   * Class names.
   */
  type Class = String
  /**
   * The map from a class to its superclass.
   */
  object superclass {
    private val tb = Map[Class, Class]()
    def insert(cls:Class, sup:Class) {tb(cls) = sup}
    def print = tb.keys.foreach(x => println(x.toString + " -> " + tb(x).toString))
    /**
     * Get a class's superclass.
     * @note The input is assumed to be a valid class name, otherwise, an exception will be thrown.
     */
    def get(cls:Class): Class = tb(cls)
  }
  
  /**
   * Interface names (abstract classes).
   */
  type Interface = Class
  /**
   * The map from a class to a list of interfaces it implements.
   */
  object interface {
    private val tb = Map[Class, List[Interface]]()
    def insert(cls:Class, intf:Interface) : Unit =
      (tb get cls) match {
        case Some(_) => tb(cls) ::= intf 
        case None => tb += (cls -> List(intf))
      }
    def print = tb.keys.foreach(x => println(x.toString + " -> " + tb(x).toString))
    /**
     * Get the list of interfaces a class implements.
     * @note Return an empty list if this class doesn't implement any interface. 
     */
    def get(cls:Class): List[Interface] = 
      if (tb contains cls) tb(cls)
      else List()
  }

  /**
   * Field names.  
   */
  type Field = String
  /**
   * The map from a class to its list of static fields.
   */
  object static_field { 
    private val tb = Map[Class, List[Field]]()
    def insert(cls:Class, fld:Field) =
      (tb get cls) match {
        case Some(_) => tb(cls) ::= fld
        case None => tb += (cls -> List(fld))
      }
    def print = tb.keys.foreach(x => println(x.toString + " -> " + tb(x).toString))
    /**
     * Get a class's static field list. 
     * @note Return an empty list if this class doesn't have any static field. 
     */
    def get(cls:Class): List[Field] = 
      if (tb contains cls) tb(cls)
      else List()
  }
  
  /**
   * The map from a class to its list of instance fields.
   */
  object instance_field { 
    private val tb = Map[Class, List[Field]]()
    def insert(cls:Class, fld:Field) =
      (tb get cls) match {
        case Some(_) => tb(cls) ::= fld
        case None => tb += (cls -> List(fld))
      }
    def print = tb.keys.foreach(x => println(x.toString + " -> " + tb(x).toString))
    /**
     * Get a class's instance field list. 
     * @note Return an empty list if this class doesn't have any instance field. 
     */
    def get(cls:Class): List[Field] = 
      if (tb contains cls) tb(cls)
      else List()
  }

  /**
   * Instruction. Format: operator, a list of targets, and a list of sources.
   */
  class Ins (var operator:String, var targets:List[String], var sources:List[String]) {
    def op = operator
    def ta: List[String] = targets
    def src: List[String] = sources
    /**
     * @param sources varied length arguments.
     */
    def this(operator:String, targets:List[String], sources:String*) = {
      this(operator, targets, sources.toList)
    }
    def this() = this("", List(), List())
    override def toString = operator + " " + targets.toString + " " + sources.toString
  }

  /**
   * Method names.
   */
  type Name = String
  /**
   * Formal arguments of methods. 
   */
  type Args = List[String]
  /**
   * Instruction labels.
   */
  type Label = String 
  /**
   * Method bodies. 
   */
  type Body = List[(Label, Ins)]
  /**
   * Registers used by a method. 
   */
  type Regs = List[String] 
  /**
   * Method definitions. 
   */
  type Method = (Args, Body, Regs)
  /**
   * Method types. 
   */
  type MtdType = String

  /**
   * The method definition table. 
   * @note A method is uniquely identified by its class, name and type. 
   */
  object method { 
    private val tb = Map[(Class, Name, MtdType), Method]()
    
    def args(cls:Class, name:Name, typ:MtdType) : Option[Args] =
      (tb get (cls,name,typ)) match {
        case Some(elem) => Some(elem._1)
        case None => None
      }
    
    def body(cls:Class, name:Name, typ:MtdType) : Option[Body] =
      (tb get (cls,name,typ)) match {
        case Some(elem) => Some(elem._2)
        case None => None
      }
   
    def regs(cls:Class, name:Name, typ:MtdType) : Option[Regs] =
      (tb get (cls,name,typ)) match {
        case Some(elem) => Some(elem._3)
        case None => None
      }
    
    /**
     *  Add a new method.
     */ 
    def insert (cls:Class, name:Name, args:Args, typ:MtdType, regs:Regs) : Unit = 
      tb += ((cls,name,typ) -> (args, List(), regs))
     
    /**
     * Insert an instruction into the body of a method.
     */ 
    def insert (cls:Class, name:Name, typ:MtdType, label:Label, ins:Ins) : Unit = {
      val body = this.body(cls,name,typ) match {
        case Some(elem) => elem
        case None => Nil
      }
      val args = this.args(cls,name,typ) match {
        case Some(elem) => elem
        case None => Nil
      }
      val regs = this.regs(cls,name,typ) match {
        case Some(elem) => elem
        case None => Nil 
      }
      tb += ((cls,name,typ) -> (args, (label, ins) :: body, regs))
    }

    /**
     * Retrieve the definition of a method.
     */
    def get (cls:Class, name:Name, typ:MtdType): Option[Method] = {
      (tb get (cls,name,typ)) match {
        case Some(elem) => Some(elem)
        case None => None 
      }
    }
    def print = tb.keys.foreach(x => println(x.toString + " -> " + tb(x).toString))
  }
  
  /**
   * Label ranges for exceptions. 
   */
  type Range = (Label, Label)
  /**
   * Except names. 
   */
  type Except = String
  /**
   * Target (instruction) labels to catch exceptions.
   */
  type Target = Label
  /**
   * A map from exceptions to target (instruction) labels. 
   */
  type Catch = (Except, Target)

  /**
   * The try-and-catch table.
   * @note Each row is uniquely identified by the quadrupe: classes, methods, method types and (instruction) label ranges.
   */
  object except {
    private val tb = Map[(Class, Name, MtdType), Map[Range, List[Catch]]]()
    def catch_list (cls:Class, name:Name, typ:MtdType, range:Range) : Option[List[Catch]] = {
      val key = (cls, name, typ)
      (tb get key) match {
        case Some(range_catch_list) => 
        (range_catch_list get range) match {
          case Some(cl) => Some(cl)
          case None => None 
        } 
        case None => None 
      }
    }
    /**
     * Add a new label range.
     */
    def insert (cls:Class, name:Name, typ:MtdType, range:Range) : Unit = {
      val key = (cls, name, typ)
      if (tb.contains(key))
        tb(key) += (range -> List[Catch]())
      else
        tb += (key -> Map(range -> List[Catch]()))
    }
    /**
     * Insert an exception-to-target map.
     */
    def insert (cls:Class, name:Name, typ:MtdType, range:Range, except:Except, target:Label) : Unit = {
      val key = (cls, name, typ)
      val cl = this.catch_list(cls, name, typ, range) match {
        case Some(cl) => cl
        case None => Nil
      }
      if (tb.contains(key))
        tb(key) += (range -> ((except, target) :: cl))
      else
        tb += (key -> Map(range -> List((except, target))))
    }
    def print = {
      for (key <- tb.keys) {
        println(key.toString + ":")
        for (range <- tb(key).keys) {
          println("\t" + range.toString + "->")
          for (except_target <- tb(key)(range))
            println("\t" + except_target.toString)
        }
      }
    } 
  }

  /**
   * Target (instruction) labels for switches.
   */
  type SwitchLabel = Label
  /**
   * The labels of switch instructions.
   */
  type OrgLabel = Label
  type Register = String

  /**
   * The switch table recording the instruction label and its dependant register.
   * @note Each row is uniquely identified by the quadrupes: classes, methods, method types and (switch instruction) labels.
   */
  object switch {
    val tb = Map[(Class, Name, MtdType, SwitchLabel), (OrgLabel, Register)]()

    def orglabel (cls:Class, name:Name, typ:MtdType, slabel:SwitchLabel) : OrgLabel =
      tb(cls, name, typ, slabel)._1
    def register (cls:Class, name:Name, typ:MtdType, slabel:SwitchLabel) : Register = 
      tb(cls, name, typ, slabel)._2
    def insert(cls:Class, name:Name, typ:MtdType, slabel:SwitchLabel, olabel:OrgLabel, reg:Register) : Unit = {
      val key = (cls, name, typ, slabel)
      tb += (key -> (olabel, reg))
    }
  }  

  /**
   * The array-data table recording the target register.
   * @note Each row is uniquely identified by the quadrupes: classes, methods, method types and (switch instruction) labels.
   */
  object array {
    val tb = Map[(Class, Name, MtdType, Label), Register]()
    def register (cls:Class, name:Name, typ:MtdType, label:Label) : Register =
      tb(cls, name, typ, label)
    def insert (cls:Class, name:Name, typ:MtdType, label:Label, reg:Register) {
      val key = (cls, name, typ, label)
      tb += (key -> reg)
    }
  }

  /**
   * Regular expressions for pattern matching, e.g., classes, methods, fields, etc.
   */
  type Pattern = Regex
  /**
   * Regular expressions for instructions, e.g., mov, new, invoke, etc.
   */
  type Operation = Regex
  type Tag = String
  /**
   * Instructions of the light Android.
   */
  type Exp = String
  type Type = Name
  type Offset = String 
  
  /**
   * Convert the output of "dexdump -d classes.dex"  to programs in light Android.
   */
  object dex {  
    private var dex_file = classes_dex_file 
    /**
     * Read switch tables and array data.
     * @note Return a list of 4-bytes integers. 
     * Ref: https://source.android.com/devices/tech/dalvik/dalvik-bytecode.html
     */
    def extra_data (offset:Offset) : List[Long] = {
      val PACKED_SWITCH_PAYLOAD = 256 // 0x0100 
      val SPARSE_SWITCH_PAYLOAD = 512 // 0x0200 
      val FILL_ARRAY_DATA_PAYLOAD = 768 // 0x0300 
      val file = new RandomAccessFile(dex_file, "r")
      // little-endian is used in Dalvik code
      def read_nbyte (n_bytes:Int): Long = { 
        var l = List[Long]()
        for (i <- 1 to n_bytes)
          l ::= file.read()
        return l.reduceLeft((x,y) => x * 256 + y) 
      }
      def read_short = read_nbyte(2)
      def read_int = read_nbyte(4)
      file.seek(offset.toInt)
      var l = List[Long]()
      val ident = read_short
      if (ident == PACKED_SWITCH_PAYLOAD) {
        val size = read_short.toInt
        read_int//first_key
        for (i <- 1 to size) 
          l ::= read_int //targets
      } else if (ident == SPARSE_SWITCH_PAYLOAD) {
        val size = read_short.toInt
        for (i <- 1 to size) 
          read_int //keys
        for (i <- 1 to size) 
          l ::= read_int //targets
      }
      else if (ident == FILL_ARRAY_DATA_PAYLOAD) {
        val elem_width = read_short.toInt
        val size = read_int.toInt
        for (i <- 1 to size)
          l ::= read_nbyte(elem_width)
      }
      file.close()
      return l.reverse
    }

    /*
     * Wei: U+10000...U+10ffff are ignored because it seems that this programming language doesn't support them.
     *      Other unicodes are from "https://source.android.com/devices/tech/dalvik/dex-format.html".
     */
    
    private val NAME:Pattern = "[a-zA-Z0-9\u00a1-\u1fff\u2010-\u2027\u2030-\ud7ff\ue000-\uffef$-_<>/\\[;]+".r
    private val STR:Pattern = "[\u00a1-\u1fff\u2010-\u2027\u2030-\ud7ff\ue000-\uffef$-_<>/\\[;\\{\\}\\(\\),#\\.\\: \"\u0000-\u00a0]*".r
    private val CLASS:Pattern = ("[ ]+Class descriptor[ ]+:[ ]+'(" + NAME.toString + ")'").r
    private val SUPPERCLASS:Pattern = ("[ ]+Superclass[ ]+:[ ]+'(" + NAME.toString + ")'").r
    private val INTERFACE:Pattern = ("[ ]+#[0-9]+[ ]+:[ ]+'(" + NAME.toString + ")'").r
    private val STATIC_FIELD:Pattern = "[ ]+Static fields[ ]+(-)".r
    private val INSTANCE_FIELD:Pattern = "[ ]+Instance fields[ ]+(-)".r
    private val METHOD:Pattern = "[ ]+Direct methods[ ]+(-)".r
    private val ITEM:Pattern = ("[ ]+name+[ ]+:[ ]+'(" + NAME.toString + ")'").r
    private val REGISTER:Pattern = ("[ ]+registers+[ ]+:[ ]+(" + NAME.toString + ")").r
    private val METHOD_TYPE:Pattern = ("[ ]+type+[ ]+:[ ]+'(\\(" + STR.toString + "\\)" + NAME.toString + ")'").r
    private val ARG_TYPE:Pattern = ("[ ]+type+[ ]+:[ ]+'\\((" + NAME.toString + ")\\)" + NAME.toString + "'").r
    
    /*
     *  Wei: I want to use the pattern
     *  
     *           ("V|(\\[*([ZBSCIJFD]|(L" + NAME.toString + ";)))").r
     *           
     *       to extract types from a string. 
     *       But it doesn't work for two consecutive "L..;".
     *       My solution is to split a string by the symbol";" then apply the following pattern.
     *       
     */
    
    private val TYPE:Pattern = ("V|(\\[*([ZBSCIJFD]|L" + NAME.toString + "))").r
    private val CODE:Pattern = ("^[0-9a-f: .]+\\|[0-9a-f]+: (" + STR.toString +")").r
    private val LABEL:Pattern = ("\\|([0-9a-f]+)").r
    private val OFFSET:Pattern = ("^([0-9a-f]+):").r
    private val CATCH_RANGE:Pattern = ("[ ]+(0x[a-z0-9]+ - 0x[a-z0-9]+$)").r
    private val CATCH:Pattern = ("^[ ]+ (" + STR.toString + " -> 0x[a-z0-9]+)").r

    private val patTag = Map[Pattern, Tag]()
    patTag += (CLASS -> "CLASS")
    patTag += (SUPPERCLASS -> "SUPERCLASS")
    patTag += (INTERFACE -> "INTERFACE")
    patTag += (STATIC_FIELD -> "STATIC_FIELD")
    patTag += (INSTANCE_FIELD -> "INSTANCE_FIELD")
    patTag += (METHOD -> "METHOD")
    patTag += (ITEM -> "ITEM")
    patTag += (REGISTER -> "REGISTER")
    patTag += (METHOD_TYPE -> "METHOD_TYPE")
    patTag += (CODE -> "CODE")
    patTag += (CATCH_RANGE -> "CATCH_RANGE")
    patTag += (CATCH -> "CATCH")
    
    private val NOP:Operation = "nop".r
    private val MOV:Operation = ("move[-/0-9a-z]* (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val MOVRESULT:Operation = ("move-result[-/0-9a-z]* (v[0-9]+)" + STR.toString).r
    private val MOVEXCEPT:Operation = ("move-exception (v[0-9]+)" + STR.toString).r
    private val RETVOID:Operation = ("return-void" + STR.toString).r
    private val RET:Operation = ("return[-/0-9a-z]* (v[0-9]+)" + STR.toString).r
    private val CONST_NUM:Operation = ("const[-/0-9a-z]* (v[0-9]+), #[a-z]+ ([a-z0-9A-Z-\\.]+) //" + STR.toString).r
    private val CONST_STR:Operation = ("const-string[-/0-9a-z]* (v[0-9]+), (" + STR.toString + ")" + STR.toString).r
    private val CONST_CLS:Operation = ("const-class[-/0-9a-z]* (v[0-9]+), (" + NAME.toString + ")" + STR.toString).r
    private val MONITOR:Operation = ("^monitor-[a-z]* (v[0-9]+)" + STR.toString).r
    private val CHECKCAST:Operation = ("check-cast (v[0-9]+), " + STR.toString).r
    private val INSTANCEOF:Operation = ("instance-of (v[0-9]+), (v[0-9]+), (" + NAME.toString + ")" + STR.toString).r
    private val ARRAYLEN:Operation = ("array-length (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val NEWI:Operation = ("new-instance (v[0-9]+), (" + NAME.toString + ")" + STR.toString).r
    private val NEWA:Operation = ("new-array (v[0-9]+), (v[0-9]+), (" + NAME.toString + ")" + STR.toString).r
    private val FILLEDNEWA:Operation = "filled-new-array[/a-z]*".r
    private val FILLARRAY:Operation = ("fill-array-data (v[0-9]+), ([a-z0-9A-Z-.]+)" + STR.toString).r
    private val PSWITCH:Operation = ("packed-switch (v[0-9]+), ([a-z0-9A-Z-.]+)" + STR.toString).r
    private val SSWITCH:Operation = ("sparse-switch (v[0-9]+), ([a-z0-9A-Z-.]+)" + STR.toString).r
    private val THROW:Operation = ("throw (v[0-9]+)" + STR.toString).r
    private val GOTO:Operation = ("goto[/0-9]* ([0-9a-f]+)" + STR.toString).r 
    private val CMP:Operation = ("cmp[-a-z]+ (v[0-9]+), (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val IF:Operation = ("if[-a-z]+ (v[0-9]+), (v[0-9]+), ([0-9a-f]+)" + STR.toString).r
    private val IFZ:Operation = ("if[-a-z]+ (v[0-9]+), ([0-9a-f]+)" + STR.toString).r
    private val AGET:Operation = ("aget[-a-z]* (v[0-9]+), (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val APUT:Operation = ("aput[-a-z]* (v[0-9]+), (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val IGET:Operation = ("iget[-a-z]* (v[0-9]+), (v[0-9]+), (" + NAME.toString + ")\\.(" + NAME.toString + "):" + STR.toString).r
    private val IPUT:Operation = ("iput[-a-z]* (v[0-9]+), (v[0-9]+), (" + NAME.toString + ")\\.(" + NAME.toString + "):" + STR.toString).r
    private val SGET:Operation = ("sget[-a-z]* (v[0-9]+), (" + NAME.toString + ")\\.(" + NAME.toString + "):" + STR.toString).r
    private val SPUT:Operation = ("sput[-a-z]* (v[0-9]+), (" + NAME.toString + ")\\.(" + NAME.toString + "):" + STR.toString).r
    private val NEG:Operation = ("neg[-a-z]+ (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val NOT:Operation = ("not[-a-z]+ (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val LONG:Operation = ("[-a-z]+to-long (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val FLOAT:Operation = ("[-a-z]+to-float (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val DOUBLE:Operation = ("[-a-z]+to-double (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val INT:Operation = ("[-a-z]+to-int (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val BYTE:Operation = ("[-a-z]+to-byte (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val CHAR:Operation = ("[-a-z]+to-char (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val SHORT:Operation = ("[-a-z]+to-short (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val ADD3:Operation = ("add[-a-z]* (v[0-9]+), (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val ADD2:Operation = ("add-[/a-z0-9]*2addr (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val ADD2L:Operation = ("add-[/a-z0-9]*lit[0-9]+ (v[0-9]+), (v[0-9]+), #[a-z]+ ([a-z0-9A-Z-.]+)" + STR.toString).r
    private val SUB3:Operation = ("sub[-a-z]* (v[0-9]+), (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val SUB2:Operation = ("sub-[/a-z0-9]*2addr (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val SUB2L:Operation = ("^rsub-[/a-z0-9]* (v[0-9]+), (v[0-9]+), #[a-z]+ ([a-z0-9A-Z-.]+)" + STR.toString).r
    private val MUL3:Operation = ("mul[-a-z]* (v[0-9]+), (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val MUL2:Operation = ("mul-[/a-z0-9]*2addr (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val MUL2L:Operation = ("mul-[/a-z0-9]*lit[0-9]+ (v[0-9]+), (v[0-9]+), #[a-z]+ ([a-z0-9A-Z-.]+)" + STR.toString).r
    private val DIV3:Operation = ("div[-a-z]* (v[0-9]+), (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val DIV2:Operation = ("div-[/a-z0-9]*2addr (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val DIV2L:Operation = ("div-[/a-z0-9]*lit[0-9]+ (v[0-9]+), (v[0-9]+), #[a-z]+ ([a-z0-9A-Z-.]+)" + STR.toString).r
    private val REM3:Operation = ("rem[-a-z]* (v[0-9]+), (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val REM2:Operation = ("rem-[/a-z0-9]*2addr (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val REM2L:Operation = ("rem-[/a-z0-9]*lit[0-9]+ (v[0-9]+), (v[0-9]+), #[a-z]+ ([a-z0-9A-Z-.]+)" + STR.toString).r
    private val AND3:Operation = ("and[-a-z]* (v[0-9]+), (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val AND2:Operation = ("and-[/a-z0-9]*2addr (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val AND2L:Operation = ("and-[/a-z0-9]*lit[0-9]+ (v[0-9]+), (v[0-9]+), #[a-z]+ ([a-z0-9A-Z-.]+)" + STR.toString).r
    private val OR3:Operation = ("^or[-a-z]* (v[0-9]+), (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val OR2:Operation = ("^or-[/a-z0-9]*2addr (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val OR2L:Operation = ("^or-[/a-z0-9]*lit[0-9]+ (v[0-9]+), (v[0-9]+), #[a-z]+ ([a-z0-9A-Z-.]+)" + STR.toString).r
    private val XOR3:Operation = ("^xor[-a-z]* (v[0-9]+), (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val XOR2:Operation = ("^xor-[/a-z0-9]*2addr (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val XOR2L:Operation = ("^xor-[/a-z0-9]*lit[0-9]+ (v[0-9]+), (v[0-9]+), #[a-z]+ ([a-z0-9A-Z-.]+)" + STR.toString).r
    private val SHL3:Operation = ("^shl[-a-z]* (v[0-9]+), (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val SHL2:Operation = ("^shl-[/a-z0-9]*2addr (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val SHL2L:Operation = ("^shl-[/a-z0-9]*lit[0-9]+ (v[0-9]+), (v[0-9]+), #[a-z]+ ([a-z0-9A-Z-.]+)" + STR.toString).r
    private val SHR3:Operation = ("^shr[-a-z]* (v[0-9]+), (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val SHR2:Operation = ("^shr-[/a-z0-9]*2addr (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val SHR2L:Operation = ("^shr-[/a-z0-9]*lit[0-9]+ (v[0-9]+), (v[0-9]+), #[a-z]+ ([a-z0-9A-Z-.]+)" + STR.toString).r
    private val USHR3:Operation = ("^ushr[-a-z]* (v[0-9]+), (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val USHR2:Operation = ("^ushr-[/a-z0-9]*2addr (v[0-9]+), (v[0-9]+)" + STR.toString).r
    private val USHR2L:Operation = ("^ushr-[/a-z0-9]*lit[0-9]+ (v[0-9]+), (v[0-9]+), #[a-z]+ ([a-z0-9A-Z-.]+)" + STR.toString).r
    private val INVOKE:Operation = "^invoke[/-a-z]*".r
    private val ARGS:Pattern = "\\{(v[0-9]+[, ]*)*\\}".r
    private val MTD:Pattern = ("}, (" + STR.toString + ")\\.(" + STR.toString + "):(" + STR.toString + ") //" + STR.toString + "$").r
    private val ARYT:Pattern = ("}, (" + NAME.toString + ") " + STR.toString + "$").r
    private val PSWITCHDATA:Operation = ("^packed-switch-data" + STR.toString).r
    private val SSWITCHDATA:Operation = ("^sparse-switch-data" + STR.toString).r
    private val ARRAYDATA:Operation = ("^array-data" + STR.toString).r
 
    
    private val opTag = Map[Operation, Tag]()
    opTag += (NOP -> "NOP")
    opTag += (MOV -> "MOV")
    opTag += (MOVRESULT -> "MOVRESULT")
    opTag += (MOVEXCEPT -> "MOVEXCEPT")
    opTag += (RETVOID -> "RETVOID")
    opTag += (RET -> "RET")
    opTag += (CONST_NUM -> "CONST_NUM")
    opTag += (CONST_STR -> "CONST_STR")
    opTag += (CONST_CLS -> "CONST_CLS")
    opTag += (MONITOR -> "MONITOR")
    opTag += (CHECKCAST -> "CHECKCAST")
    opTag += (INSTANCEOF -> "INSTANCEOF")
    opTag += (ARRAYLEN -> "ARRAYLEN")
    opTag += (NEWI -> "NEWI")
    opTag += (NEWA -> "NEWA")
    opTag += (FILLEDNEWA -> "FILLEDNEWA")
    opTag += (FILLARRAY -> "FILLARRAY")
    opTag += (PSWITCH -> "PSWITCH")
    opTag += (SSWITCH -> "SSWITCH")
    opTag += (THROW -> "THROW")
    opTag += (GOTO -> "GOTO")
    opTag += (CMP -> "CMP")
    opTag += (IF -> "IF")
    opTag += (IFZ -> "IFZ")
    opTag += (AGET -> "AGET")
    opTag += (APUT -> "APUT")
    opTag += (IGET -> "IGET")
    opTag += (IPUT -> "IPUT")
    opTag += (SGET -> "SGET")
    opTag += (SPUT -> "SPUT")
    opTag += (INVOKE -> "INVOKE")
    opTag += (NEG -> "NEG")
    opTag += (NOT -> "NOT")
    opTag += (LONG -> "LONG")
    opTag += (FLOAT -> "FLOAT")
    opTag += (DOUBLE -> "DOUBLE")
    opTag += (INT -> "INT")
    opTag += (BYTE -> "BYTE")
    opTag += (CHAR -> "CHAR")
    opTag += (SHORT -> "SHORT")
    opTag += (ADD3 -> "ADD3")
    opTag += (ADD2 -> "ADD2")
    opTag += (ADD2L -> "ADD2L")
    opTag += (SUB3 -> "SUB3")
    opTag += (SUB2 -> "SUB2")
    opTag += (SUB2L -> "SUB2L")
    opTag += (MUL3 -> "MUL3")
    opTag += (MUL2 -> "MUL2")
    opTag += (MUL2L -> "MUL2L")
    opTag += (DIV3 -> "DIV3")
    opTag += (DIV2 -> "DIV2")
    opTag += (DIV2L -> "DIV2L")
    opTag += (REM3 -> "REM3")
    opTag += (REM2 -> "REM2")
    opTag += (REM2L -> "REM2L")
    opTag += (AND3 -> "AND3")
    opTag += (AND2 -> "AND2")
    opTag += (AND2L -> "AND2L")
    opTag += (OR3 -> "OR3")
    opTag += (OR2 -> "OR2")
    opTag += (OR2L -> "OR2L")
    opTag += (XOR3 -> "XOR3")
    opTag += (XOR2 -> "XOR2")
    opTag += (XOR2L -> "XOR2L")
    opTag += (SHL3 -> "SHL3")
    opTag += (SHL2 -> "SHL2")
    opTag += (SHL2L -> "SHL2L")
    opTag += (SHR3 -> "SHR3")
    opTag += (SHR2 -> "SHR2")
    opTag += (SHR2L -> "SHR2L")
    opTag += (USHR3 -> "USHR3")
    opTag += (USHR2 -> "USHR2")
    opTag += (USHR2L -> "USHR2L")
    opTag += (PSWITCHDATA -> "PSWITCHDATA")
    opTag += (SSWITCHDATA -> "SSWITCHDATA")
    opTag += (ARRAYDATA -> "ARRAYDATA")

    private val opExp = Map[Operation, Exp]()
    opExp += (NOP -> "op")
    opExp += (MOV -> "mov")
    opExp += (MOVRESULT -> "mov")
    opExp += (MOVEXCEPT -> "op")
    opExp += (RETVOID -> "ret")
    opExp += (RET -> "ret")
    opExp += (CONST_NUM -> "mov")
    opExp += (CONST_STR -> "mov")
    opExp += (CONST_CLS -> "mov")
    opExp += (MONITOR -> "op")
    opExp += (CHECKCAST -> "op")
    opExp += (INSTANCEOF -> "op")
    opExp += (ARRAYLEN -> "op")
    opExp += (NEWI -> "new")
    opExp += (NEWA -> "new")
    opExp += (FILLEDNEWA -> "new")
    opExp += (FILLARRAY -> "fillarray")
    opExp += (PSWITCH -> "switch")
    opExp += (SSWITCH -> "switch")
    opExp += (THROW -> "ret")
    opExp += (GOTO -> "jmp")
    opExp += (CMP -> "op")
    opExp += (IF -> "jmp")
    opExp += (IFZ -> "jmp")
    opExp += (AGET -> "mov")
    opExp += (APUT -> "mov")
    opExp += (IGET -> "mov")
    opExp += (IPUT -> "mov")
    opExp += (SGET -> "mov")
    opExp += (SPUT -> "mov")
    opExp += (INVOKE -> "inv")
    opExp += (NEG -> "op")
    opExp += (NOT -> "op")
    opExp += (LONG -> "op")
    opExp += (FLOAT -> "op")
    opExp += (DOUBLE -> "op")
    opExp += (INT -> "op")
    opExp += (BYTE -> "op")
    opExp += (CHAR -> "op")
    opExp += (SHORT -> "op")
    opExp += (ADD3 -> "op")
    opExp += (ADD2 -> "op")
    opExp += (ADD2L -> "op")
    opExp += (SUB3 -> "op")
    opExp += (SUB2 -> "op")
    opExp += (SUB2L -> "op")
    opExp += (MUL3 -> "op")
    opExp += (MUL2 -> "op")
    opExp += (MUL2L -> "op")
    opExp += (DIV3 -> "op")
    opExp += (DIV2 -> "op")
    opExp += (DIV2L -> "op")
    opExp += (REM3 -> "op")
    opExp += (REM2 -> "op")
    opExp += (REM2L -> "op")
    opExp += (AND3 -> "op")
    opExp += (AND2 -> "op")
    opExp += (AND2L -> "op")
    opExp += (OR3 -> "op")
    opExp += (OR2 -> "op")
    opExp += (OR2L -> "op")
    opExp += (XOR3 -> "op")
    opExp += (XOR2 -> "op")
    opExp += (XOR2L -> "op")
    opExp += (SHL3 -> "op")
    opExp += (SHL2 -> "op")
    opExp += (SHL2L -> "op")
    opExp += (SHR3 -> "op")
    opExp += (SHR2 -> "op")
    opExp += (SHR2L -> "op")
    opExp += (USHR3 -> "op")
    opExp += (USHR2 -> "op")
    opExp += (USHR2L -> "op")
    opExp += (PSWITCHDATA -> "psd")
    opExp += (SSWITCHDATA -> "ssd")
    opExp += (ARRAYDATA -> "ad")

    /**
     * Opcode names
     */
    type Op = String
    /**
     * Decode Dalvik opcodes and translate them into instructions in light Android.
     * @note Ref: https://source.android.com/devices/tech/dalvik/dalvik-bytecode.html
     */
    def decode_op (ops: Op) : Option[Ins] = {
      var ins:Option[Ins] = None 
      val def_reg = "v"
      opTag.keys.foreach(op =>
        op.findFirstIn(ops) match {
          case None =>
          case Some(_) =>
            opTag(op) match {
              case "NOP" => ins = Some(new Ins(opExp(op), List()))
              case "MOV" => val op(t,s) = ops; ins = Some(new Ins(opExp(op), List(t), s))
              case "MOVRESULT" => val op(t) = ops; ins = Some(new Ins(opExp(op), List(t), def_reg))
              case "MOVEXCEPT" => ins = Some(new Ins(opExp(op), List()))
              case "RETVOID" => ins = Some(new Ins(opExp(op), List()))
              case "RET" => val op(s) = ops; ins = Some(new Ins (opExp(op), List(), s))
              case "CONST_NUM" => val op(t,s) = ops; ins = Some(new Ins(opExp(op), List(t), s))
              case "CONST_STR" => val op(t,s) = ops; ins = Some(new Ins(opExp(op), List(t), s))
              case "CONST_CLS" => val op(t,c) = ops; ins = Some(new Ins(opExp(op), List(t), c))
              case "MONITOR" => val op(s) = ops; ins = Some(new Ins(opExp(op), List()))
              case "CHECKCAST" => ins = Some(new Ins(opExp(op), List()))
              case "INSTANCEOF" => val op(t,s,c) = ops; ins = Some(new Ins(opExp(op), List(t), s, c))
              case "ARRAYLEN" => val op(t,s) = ops; ins = Some(new Ins(opExp(op), List(t), s))
              case "NEWI" => val op(t,c) = ops; ins = Some(new Ins(opExp(op), List(t), c))
              case "NEWA" => val op(t,n,c) = ops; ins = Some(new Ins(opExp(op), List(t), n))
              case "FILLEDNEWA" => 
                val args = ARGS.findFirstIn(ops) match {
                  // e.g., {v1, v2, v3}
                  case Some(args) => args.substring(1, args.length-1).split(", ").toList
                  case None => List()
                }
                val arty = ARYT.findFirstIn(ops) match {
                  case Some(ARYT(name)) => List(name)
                  case None => List()
                }
                ins = Some(new Ins(opExp(op), List(def_reg), args.length.toString :: args))
              case "FILLARRAY" => val op(t,l) = ops; ins = Some(new Ins(opExp(op), List(t), Integer.parseInt(l,16).toString))
              case "THROW" => ins = Some(new Ins(opExp(op), List()))
              case "GOTO" => val op(l) = ops; ins = Some(new Ins(opExp(op), List(Integer.parseInt(l,16).toString)))
              case "PSWITCH" => val op(s,l) = ops; ins = Some(new Ins(opExp(op), List(Integer.parseInt(l,16).toString), s))
              case "SSWITCH" => val op(s,l) = ops; ins = Some(new Ins(opExp(op), List(Integer.parseInt(l,16).toString), s))
              case "CMP" => val op(t,s0,s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "IF" => val op(s0,s1,l) = ops; ins = Some(new Ins(opExp(op), List(Integer.parseInt(l,16).toString), s0, s1))
              case "IFZ" => val op(s,l) = ops; ins = Some(new Ins(opExp(op), List(Integer.parseInt(l,16).toString), s))
              case "AGET" => val op(t, a, i) = ops; ins = Some(new Ins(opExp(op), List(t), a + "[" + i + "]"))
              case "APUT" => val op(s, a, i) = ops; ins = Some(new Ins(opExp(op), List(a + "[" + i + "]"), s))
              case "IGET" => val op(t, o, c, f) = ops; ins = Some(new Ins(opExp(op), List(t), o + "." + f))
              case "IPUT" => val op(s, o, c, f) = ops; ins = Some(new Ins(opExp(op), List(o + "." + f), s))
              case "SGET" => val op(t, c, f) = ops; ins = Some(new Ins(opExp(op), List(t), c + "." + f))
              case "SPUT" => val op(s, c, f) = ops; ins = Some(new Ins(opExp(op), List(c + "." + f), s))
              case "INVOKE" => 
                val args = ARGS.findFirstIn(ops) match {
                  // e.g., {v1, v2, v3}
                  case Some(args) => args.substring(1, args.length-1).split(", ").toList
                  case None => List()
                }
                val mtd = MTD.findFirstIn(ops) match {
                  case Some(MTD(cls,name,typ)) => List(cls, name, typ)
                  case None => List()
                }
                ins = Some(new Ins(opExp(op), List(def_reg),  mtd ++ args))
              case "NEG" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), s))
              case "NOT" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), s))
              case "LONG" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), s))
              case "FLOAT" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), s))
              case "DOUBLE" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), s))
              case "INT" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), s))
              case "BYTE" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), s))
              case "CHAR" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), s))
              case "SHORT" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), s))
              case "ADD3" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "ADD2" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), t, s))
              case "ADD2L" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "SUB3" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "SUB2" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), t, s))
              case "SUB2L" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "MUL3" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "MUL2" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), t, s))
              case "MUL2L" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "DIV3" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "DIV2" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), t, s))
              case "DIV2L" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "REM3" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "REM2" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), t, s))
              case "REM2L" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "AND3" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "AND2" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), t, s))
              case "AND2L" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "OR3" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "OR2" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), t, s))
              case "OR2L" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "XOR3" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "XOR2" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), t, s))
              case "XOR2L" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "SHL3" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "SHL2" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), t, s))
              case "SHL2L" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "SHR3" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "SHR2" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), t, s))
              case "SHR2L" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "USHR3" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "USHR2" => val op(t, s) = ops; ins = Some(new Ins(opExp(op), List(t), t, s))
              case "USHR2L" => val op(t, s0, s1) = ops; ins = Some(new Ins(opExp(op), List(t), s0, s1))
              case "PSWITCHDATA" => ins = Some(new Ins(opExp(op), List()))
              case "SSWITCHDATA" => ins = Some(new Ins(opExp(op), List()))
              case "ARRAYDATA" => ins = Some(new Ins(opExp(op), List()))
            }
        })
      return ins
    }
    
    private var cls:Class = ""
    private var in_static_field_list:Boolean = false
    private var in_instance_field_list:Boolean = false
    private var mtd:Name = ""
    private var typ:Type = ""
    private var num_regs = 0
    private var num_args = 0
    private var args = List[String]()
    private var regs = List[String]()
    private var ins : Ins = new Ins
    private var offset:Offset = "" 
    private var label:Label = "" 
    private var start_label:Label = "" 
    private var end_label:Label = "" 
    

    /**
     * Decode Dalvik code (output of "dexdump -d classes.dex") by lines. 
     */
    def decode_line (line:String) : Unit = {
      var found_pattern:Boolean = false
      for (pat <- patTag.keys) {
        pat.findFirstIn(line) match {
          case None =>
          case Some(pat(name)) =>
            found_pattern = true
            patTag(pat) match {
              case "CLASS" => cls = name
              case "SUPERCLASS" => superclass.insert(cls, name)
              case "INTERFACE" => interface.insert(cls, name)
              case "STATIC_FIELD" => in_static_field_list = true
              case "INSTANCE_FIELD" => in_static_field_list = false; in_instance_field_list = true
              case "METHOD" => in_instance_field_list = false
              case "ITEM" =>
                if (in_static_field_list) //a new static field name
                  static_field.insert(cls, name)
                else if (in_instance_field_list) //a new instance field name
                  instance_field.insert(cls, name)
                else // a new method name
                  mtd = name; typ = ""; num_regs = 0; num_args = 0
              case "METHOD_TYPE" =>
                typ = name
                // the number of formal arguments of a method
                num_args = ARG_TYPE.findFirstIn(line) match {
                  case Some(ARG_TYPE(argTyp)) => 
                    argTyp.split(";").map(x => TYPE.findAllIn(x).length).reduceLeft(_+_).toInt
                  case None => 0 //no formal argument
                }
              case "REGISTER" =>
                // the number of registers used by a method
                num_regs = name.toInt
                /*
                 * Wei: In Dalvik code the last num_args registers are used to store the values of
                 *      arguments of a method. The register number starts from 0.
                 *      All methods in classes have a default argument: this.
                 */
                args = ((num_regs - num_args - 1) to (num_regs - 1) toList).map(x => "v" + x.toString)
                regs = (0 to (num_regs - 1) toList).map(x => "v" + x.toString)
                method.insert(cls, mtd, args, typ, regs)
              case "CODE" =>
                OFFSET.findFirstIn(line) match {
                  case Some(name) => offset = Integer.parseInt(name.substring(0, name.length - 1), 16).toString //remove the symbol ":"
                  case None =>
                }
                LABEL.findFirstIn(line) match {
                  case Some(name) => label = Integer.parseInt(name.substring(1), 16).toString //remove the symbol "|"
                  case None =>
                }
                decode_op(name) match {
                  case Some(elem) => ins = elem
                  case None =>
                }
                // deal with *-switch and fill-array-data
                val operator = ins.op
                val targets = ins.ta
                val sources = ins.src
                if (operator == "switch") { // packed or sparse switch 
                  val switch_label = targets.head 
                  val original_label = label
                  val register = sources.head
                  switch.insert(cls, mtd, typ, switch_label, original_label, register) 
                  ins = new Ins("jmp", List(switch_label))
                } else if (operator == "psd" || operator == "ssd") { // packed or sparse switch data
                  val switch_label = label 
                  val register =  switch.register(cls, mtd, typ, switch_label)
                  val original_label = switch.orglabel(cls, mtd, typ, switch_label) 
                  var target_labels = List[String]() 
                  for (t <- extra_data(offset))
                    target_labels ::= (t + original_label.toLong).toString
                  ins = new Ins("jmp", target_labels, List(register))
                } else if (operator == "fillarray") { // fill-array-data
                  val array_data_label = sources.head 
                  val register = targets.head
                  array.insert(cls, mtd, typ, array_data_label, register)
                  ins = new Ins("jmp", List(array_data_label))
                } else if (operator == "ad") {
                  val array_data_label = label 
                  val register = array.register(cls, mtd, typ, array_data_label)
                  var array_data = List[String]() 
                  for (t <- extra_data(offset))
                    array_data ::= t.toString
                  array_data = array_data.reverse
                  ins = new Ins("new", List(register), array_data.length.toString :: array_data)
                }
                method.insert(cls, mtd, typ, label, ins)
              case "CATCH_RANGE" => 
                val Array(start, end) =  name.split(" - ")
                start_label = Integer.parseInt(start.substring(2), 16).toString //remove "0x"
                end_label = Integer.parseInt(end.substring(2), 16).toString //remove "0x"
                except.insert(cls, mtd, typ, (start_label, end_label))
              case "CATCH" => 
                val Array(exception, label) =  name.split(" -> ")
                val target = Integer.parseInt(label.substring(2), 16).toString //remove "0x"
                except.insert(cls, mtd, typ, (start_label, end_label), exception, target)
            }
        }
      }
      //debugging: if (!found_pattern) println(line) 
    }
  }

  // deal with unicode
  import java.nio.charset.CodingErrorAction
  import scala.io.Codec
  implicit val codec = Codec("UTF-8")
  codec.onMalformedInput(CodingErrorAction.REPLACE)
  codec.onUnmappableCharacter(CodingErrorAction.REPLACE)
 
  for (line <- Source.fromFile(dex_dump_file).getLines()) {
    dex.decode_line(line)
  }
}
