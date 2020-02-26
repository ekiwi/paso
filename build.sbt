name := "paso"
version := "0.1"
scalaVersion := "2.12.10"

resolvers ++= Seq(Resolver.sonatypeRepo("snapshots"), Resolver.sonatypeRepo("releases"))

scalacOptions := Seq("-deprecation", "-unchecked", "-Xsource:2.11")

libraryDependencies += "edu.berkeley.cs" %% "chisel3" % "3.2.+"
libraryDependencies += "edu.berkeley.cs" %% "firrtl" % "1.2.+"
libraryDependencies += "edu.berkeley.cs" %% "chiseltest" % "0.2-SNAPSHOT" % "test"
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.1" withSources()

scalaSource in Compile := baseDirectory.value / "src"
scalaSource in Test := baseDirectory.value / "test"
