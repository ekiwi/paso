name := "paso"
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
pomIncludeRepository := { _ => false }
homepage := Some(url("https://github.com/ekiwi/paso"))
licenses := Seq("BSD-style" -> url("http://www.opensource.org/licenses/bsd-license.php"))
scmInfo := Some(
  ScmInfo(
    url("https://github.com/ekiwi/paso.git"),
    "scm:git:git@github.com:ekiwi/paso.git"
  )
)
developers := List(
  Developer("ekiwi", "Kevin Laeufer", "laeufer@berkeley.edu", url("https://github.com/ekiwi"))
)

// it seems like currently github packages does not support SNAPSHOT
// releases for source and docs:
// https://github.community/t5/GitHub-API-Development-and/Github-Package-snapshot-build-number-not-updating/td-p/49012
packageDoc / publishArtifact := false
packageSrc / publishArtifact := false

// the version is derrived from the git tag:
// https://github.com/dwijnand/sbt-dynver
//version := "0.1-SNAPSHOT"
// replaceing '+' with '-' seems to fix some problems with pushing the jar
// from a github action
// java.io.IOException: Error writing to server
// at sun.net.www.protocol.http.HttpURLConnection.writeRequests(HttpURLConnection.java:700)
dynverSeparator in ThisBuild := "-"

// derrived from looking at:
// https://github.com/djspiewak/sbt-github-packages/blob/master/src/main/scala/sbtghpackages/GitHubPackagesPlugin.scala
val realm = "GitHub Package Registry"
val ghurl = "https://maven.pkg.github.com/ekiwi/paso"
publishTo := Some(realm at ghurl)
credentials ++= sys.env.get("GITHUB_TOKEN").map(t => Credentials(realm, "maven.pkg.github.com", "_", t))

