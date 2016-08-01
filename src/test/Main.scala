package test
import lang.LightAndroid

object Main extends App {
  val work_dir = "/Users/weichen/exp/temp"
  val classes_dex_file = work_dir + "/classes.dex"
  val dex_dump_file = work_dir + "/dex_dump.txt"
  val la = new LightAndroid(classes_dex_file, dex_dump_file)
  println(la.static_field.get("Ljava/lang/Object;"))
  println(la.static_field.get("Lcom/app/demo/MainActivity;"))
  println(la.interface.get("Lcom/app/demo/MainActivity;"))
  println(la.method.args("Lcom/app/demo/MainActivity;", "gcd", "(II)V").toString)
  println(la.method.body("Lcom/app/demo/MainActivity;", "gcd", "(II)V").toString)
}
