name := "paso"
version := "0.1"
scalaVersion := "2.13.1"

scalacOptions := Seq("-deprecation", "-unchecked", "-Xsource:2.11")

libraryDependencies += "edu.berkeley.cs" %% "chisel3" % "3.2.+"
libraryDependencies += "edu.berkeley.cs" %% "firrtl" % "1.2.+"

scalaSource in Compile := baseDirectory.value / "src"
scalaSource in Test := baseDirectory.value / "test"
