package test
import lang.LightAndroid

object Main extends App {
  val work_dir = "/Users/weichen/exp/temp"
  val classes_dex_file = work_dir + "/classes.dex"
  val dex_dump_file = work_dir + "/dex_dump.txt"
  val la = new LightAndroid(classes_dex_file, dex_dump_file)
  println(la.interface.get("Landroid/support/annotation/IntRange;"))
  println(la.interface.get("Lcom/app/demo/MainActivity;"))
}
