name := "loco"

version := "0.1"

scalaVersion := "2.11.6"

libraryDependencies ++= Seq(
  "org.scalatest" % "scalatest_2.11" % "2.2.4" % "test",
  "junit" % "junit" % "4.10" % "test",
  "org.scalaz" %% "scalaz-core" % "7.1.2"
)

testOptions in Test += Tests.Argument("-oF")

// scalacOptions ++= Seq("-feature", "-language:higherKinds")
