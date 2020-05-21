name := "paso"
version := "0.1-SNAPSHOT"
scalaVersion := "2.12.10"

resolvers ++= Seq(Resolver.sonatypeRepo("snapshots"), Resolver.sonatypeRepo("releases"))
scalacOptions := Seq("-deprecation", "-unchecked", "-Xsource:2.11")

libraryDependencies += "edu.berkeley.cs" %% "chisel3" % "3.3.0-RC2"
libraryDependencies += "edu.berkeley.cs" %% "firrtl" % "1.3.0-RC2"
libraryDependencies += "edu.berkeley.cs" %% "chiseltest" % "0.2.0-RC2" % "test"
// required for uclid files
libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.9.0"
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.1" withSources()

// execute test in serial for now to avoid race conditions on shared files like test.btor
parallelExecution := false

scalaSource in Compile := baseDirectory.value / "src"
scalaSource in Test := baseDirectory.value / "test"
resourceDirectory in Test := baseDirectory.value / "test" / "resources"

// publication settings
publishMavenStyle := true
publishArtifact in Test := false
pomIncludeRepository := { x => false }
pomExtra := (
<url>https://github.com/ekiwi/paso</url>
<licenses>
  <license>
    <name>BSD-style</name>
    <url>http://www.opensource.org/licenses/bsd-license.php</url>
    <distribution>repo</distribution>
  </license>
</licenses>
<scm>
  <url>https://github.com/ekiwi/paso.git</url>
  <connection>scm:git:github.com/ekiwi/paso.git</connection>
</scm>
<developers>
  <developer>
    <id>ekiwi</id>
    <name>Kevin Laeufer</name>
  </developer>
</developers>
)
