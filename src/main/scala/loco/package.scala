package object loco {

  def intsFrom(i: Int): Stream[Int] = i #:: intsFrom(i+1)
  val nats = intsFrom(0).map(_.toString)
  // stdlib bug; should just use filterNot when they make lazy again
  def freshVar(prohib: Set[String]) = nats.filter(!prohib(_)).head

}
