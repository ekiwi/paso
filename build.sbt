val basicSettings = Seq(
  name := "paso",
  organization := "edu.berkeley.cs",
  scalaVersion := "2.12.10",
  scalaSource in Compile := baseDirectory.value / "src",
  scalaSource in Test := baseDirectory.value / "test",
  resourceDirectory in Test := baseDirectory.value / "test" / "resources",
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
  // for structural bundles
  scalacOptions := Seq("-deprecation", "-unchecked", "-Xsource:2.11"),
  libraryDependencies += "edu.berkeley.cs" %% "chisel3" % "3.4.0-RC1",
)

val otherDependencySettings = Seq(
  libraryDependencies += "edu.berkeley.cs" %% "chiseltest" % "0.3.0-RC1" % "test",
  // required for uclid files
  libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.9.0",
  libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.1" withSources(),
  // JNA for SMT Solver bindings
  libraryDependencies += "net.java.dev.jna" % "jna" % "5.4.0",
  libraryDependencies += "net.java.dev.jna" % "jna-platform" % "5.4.0",
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
  packageSrc / publishArtifact := false,

  // derrived from looking at:
  // https://github.com/djspiewak/sbt-github-packages/blob/master/src/main/scala/sbtghpackages/GitHubPackagesPlugin.scala
  publishTo := Some(ghrealm at ghurl),
  credentials ++= sys.env.get("GITHUB_TOKEN").map(t => Credentials(ghrealm, "maven.pkg.github.com", "_", t)),
)

lazy val paso = (project in file("."))
  .settings(basicSettings)
  .settings(versionSettings)
  .settings(chiselSettings)
  .settings(otherDependencySettings)
  .settings(pubSettings)
  .settings(
    // execute test in serial for now to avoid race conditions on shared files like test.btor
    parallelExecution := false,
  )

lazy val benchmarks = (project in file("benchmarks"))
  .dependsOn(paso)
  .settings(chiselSettings)
  .settings(
    scalaSource in Compile := baseDirectory.value / "src",
    assemblyJarName in assembly := "paso-benchmarks.jar",
    test in assembly := {},
  )
