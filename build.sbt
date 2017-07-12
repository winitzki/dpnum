
val scalaV = "2.12.2"

lazy val root = (project in file(".")).aggregate(dpint)

lazy val dpint = (project in file("dpint"))
  .settings(
     name := "dpint"
, scalaVersion := scalaV
, libraryDependencies ++= Seq(
"org.scalatest" %% "scalatest" % "3.0.3" % Test
)
)

