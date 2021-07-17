val basicSettings = Seq(
  name := "paso",
  organization := "edu.berkeley.cs",
)

lazy val isAtLeastScala213 = Def.setting {
  import Ordering.Implicits._
  CrossVersion.partialVersion(scalaVersion.value).exists(_ >= (2, 13))
}


val directoryLayout = Seq(
  scalaSource in Compile := baseDirectory.value / "src",
  resourceDirectory in Compile := baseDirectory.value / "src" / "resources",
  scalaSource in Test := baseDirectory.value / "test",
  resourceDirectory in Test := baseDirectory.value / "test" / "resources",
)

val compilerSettings = Seq(
  scalaVersion := "2.13.5",
  crossScalaVersions := Seq("2.12.13", "2.13.5"),
  scalacOptions := Seq("-deprecation", "-unchecked", "-language:reflectiveCalls", "-Xcheckinit"),
)

val versionSettings = Seq(
  // the version is derrived from the git tag:
  // https://github.com/dwijnand/sbt-dynver
  //version := "0.1-SNAPSHOT"
  // replaceing '+' with '-' seems to fix some problems with pushing the jar
  // from a github action
  // java.io.IOException: Error writing to server
  // at sun.net.www.protocol.http.HttpURLConnection.writeRequests(HttpURLConnection.java:700)
  dynverSeparator in ThisBuild := "-"
)

val chiselSettings = Seq(
  resolvers ++= Seq(Resolver.sonatypeRepo("snapshots")),
  libraryDependencies += "edu.berkeley.cs" %% "chisel3" % "3.5-SNAPSHOT",
  addCompilerPlugin("edu.berkeley.cs" % "chisel3-plugin" % "3.5-SNAPSHOT" cross CrossVersion.full),
)

val otherDependencySettings = Seq(
  // treadle is used for concrete exectuion of untimed modules
  libraryDependencies += "edu.berkeley.cs" %% "treadle" % "1.5-SNAPSHOT",
  // SMT library
  libraryDependencies += "edu.berkeley.cs" %% "maltese-smt" % "0.5-SNAPSHOT",
  // we depend on scalatest for the [[paso.PasoTester]]
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.0",
  // JNA for SMT Solver bindings
  libraryDependencies += "net.java.dev.jna" % "jna" % "5.4.0",
  libraryDependencies += "net.java.dev.jna" % "jna-platform" % "5.4.0",
  // BDDs for protocol guards
  libraryDependencies += "com.github.com-github-javabdd" % "com.github.javabdd" % "1.0.1",
)

val testDependencySettings = Seq(
  // libraryDependencies += "edu.berkeley.cs" %% "chiseltest" % "0.5-SNAPSHOT" % "test",
)

val ghrealm = "GitHub Package Registry"
val ghurl = "https://maven.pkg.github.com/ekiwi/paso"

lazy val pubSettings = Seq(
  // publication settings
  publishMavenStyle := true,
  publishArtifact in Test := false,
  pomIncludeRepository := { _ => false },
  homepage := Some(url("https://github.com/ekiwi/paso")),
  licenses := Seq("BSD-style" -> url("http://www.opensource.org/licenses/bsd-license.php")),
  scmInfo := Some(
    ScmInfo(
      url("https://github.com/ekiwi/paso.git"),
      "scm:git:git@github.com:ekiwi/paso.git"
    )
  ),
  developers := List(
    Developer("ekiwi", "Kevin Laeufer", "laeufer@berkeley.edu", url("https://github.com/ekiwi"))
  ),
  // it seems like currently github packages does not support SNAPSHOT
  // releases for source and docs:
  // https://github.community/t5/GitHub-API-Development-and/Github-Package-snapshot-build-number-not-updating/td-p/49012
  packageDoc / publishArtifact := false,

  // derrived from looking at:
  // https://github.com/djspiewak/sbt-github-packages/blob/master/src/main/scala/sbtghpackages/GitHubPackagesPlugin.scala
  publishTo := Some(ghrealm at ghurl),
  credentials ++= sys.env.get("GITHUB_TOKEN").map(t => Credentials(ghrealm, "maven.pkg.github.com", "_", t)),
)

lazy val paso = (project in file("."))
  .settings(basicSettings)
  .settings(compilerSettings)
  .settings(directoryLayout)
  .settings(versionSettings)
  .settings(chiselSettings)
  .settings(testDependencySettings)
  .settings(otherDependencySettings)
  .settings(pubSettings)
  .settings(
    // execute test in serial for now to avoid race conditions on shared files like test.btor
    parallelExecution := false,
  )

lazy val benchmarks = (project in file("benchmarks"))
  .dependsOn(paso)
  .settings(compilerSettings)
  .settings(directoryLayout)
  .settings(chiselSettings)
  .settings(testDependencySettings)
  .settings(
    assemblyJarName in assembly := "paso-benchmarks.jar",
    test in assembly := {},
  )
  .settings(
    // execute test in serial for now to avoid race conditions on shared files like test.btor
    parallelExecution := false,
  )
