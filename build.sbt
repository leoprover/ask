lazy val commonSettings = Seq(
  organization := "org.leo",
  version := "0.1.0-SNAPSHOT",
  scalaVersion := "2.13.14",
  scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
    ),
  licenses += "MIT" -> url("https://opensource.org/license/MIT"),

  libraryDependencies += "io.github.leoprover" %% "scala-tptp-parser" % "1.7.1"
)

lazy val embedding = (project in file("."))
  .disablePlugins(sbtassembly.AssemblyPlugin)
  .settings(
    commonSettings,
    name := "ASk",
    description := "Alex' Skolemizer",
  ).aggregate(runtime, app)

lazy val runtime = (project in file("ask-runtime"))
	.settings(
	  commonSettings,
    name := "ASk-runtime",
    assembly / assemblyOption ~= {
      _.withIncludeScala(false)
    },
    assembly/test := {},
    assembly/assemblyJarName := s"${name.value}-${version.value}.jar",
    unmanagedBase := baseDirectory.value / ".." / "lib"
	)

lazy val app = (project in file("ask-app"))
  .enablePlugins(NativeImagePlugin)
	.settings(
	  commonSettings,
    name := "ASk-app",
    Compile/mainClass := Some("leo.modules.ASk"),
    assembly/mainClass := Some("leo.modules.ASk"),
    assembly/assemblyJarName := s"${name.value}-${version.value}.jar",
    assembly/test := {},
    unmanagedBase := baseDirectory.value / ".." / "lib"
	).dependsOn(runtime)

