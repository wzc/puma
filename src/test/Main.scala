package test
import lang.LightAndroid
import lang.Lambda
import effect.Tiny

object Main extends App {

  val work_dir = "/Users/weichen/exp/temp"
  val classes_dex_file = work_dir + "/classes.dex"
  val dex_dump_file = work_dir + "/dex_dump.txt"
  val la = new LightAndroid(classes_dex_file, dex_dump_file)
  val bd = la.method.body("Lcom/app/demo/MainActivity;", "gcd", "(II)V")
  val x = new Lambda()
 

  /*


  println(la.static_field.get("Ljava/lang/Object;"))
  println(la.static_field.get("Lcom/app/demo/MainActivity;"))
  println(la.interface.get("Lcom/app/demo/MainActivity;"))
  println(la.method.args("Lcom/app/demo/MainActivity;", "gcd", "(II)V").toString)
  println(la.method.body("Lcom/app/demo/MainActivity;", "gcd", "(II)V").toString)
  println(la.method.regs("Lcom/app/demo/MainActivity;", "gcd", "(II)V").toString)
  println(la.method.body("Landroid/support/graphics/drawable/PathParser;", "copyOfRange", "([FII)[F").toString)
  val work_dir = "/Users/weichen/exp/temp"
  var prg_file = work_dir + "/loop.tiny"
  println(prg_file)
  var tiny = new Tiny(prg_file)
  prg_file = work_dir + "/recursion.tiny"
  println(prg_file)
  tiny = new Tiny(prg_file)
  prg_file = work_dir + "/mutual-recursion.tiny"
  println(prg_file)
  tiny = new Tiny(prg_file)
  prg_file = work_dir + "/context-sensitive.tiny"
  println(prg_file)
  tiny = new Tiny(prg_file)
  prg_file = work_dir + "/flow-sensitive.tiny"
  println(prg_file)
  tiny = new Tiny(prg_file)
  prg_file = work_dir + "/source-to-sink.tiny"
  println(prg_file)
  tiny = new Tiny(prg_file)
  */
}
