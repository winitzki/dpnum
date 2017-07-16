
val scalaV = "2.12.2"

lazy val dpnum_root = (project in file(".")).aggregate(dpint)

lazy val dpint = (project in file("dpint"))
  .settings(
    name := "dpint"
    , scalaVersion := scalaV
    , libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % "3.0.3" % Test
      , "org.typelevel" %% "spire" % "0.14.1"
      , "org.scalacheck" %% "scalacheck" % "1.13.5" % Test
    )
  )

