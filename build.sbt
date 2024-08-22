lazy val commonSettings = Seq(
  organization := "org.leo",
  version := "0.2.1",
  scalaVersion := "2.13.14",
  scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
    ),
  licenses += "MIT" -> url("https://opensource.org/license/MIT"),
  resolvers ++= Resolver.sonatypeOssRepos("snapshots"),
  libraryDependencies += "io.github.leoprover" %% "scala-tptp-parser" % "1.7.1+3-49425aa8-SNAPSHOT"
)

lazy val embedding = (project in file("."))
  .disablePlugins(sbtassembly.AssemblyPlugin)
  .settings(
    commonSettings,
    name := "ask",
    description := "Alex' Skolemizer",
  ).aggregate(runtime, app)

lazy val runtime = (project in file("ask-runtime"))
	.settings(
	  commonSettings,
    name := "ask-runtime",
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
    name := "ask-app",
    Compile/mainClass := Some("leo.modules.ASkApp"),
    assembly/mainClass := Some("leo.modules.ASkApp"),
    assembly/assemblyJarName := s"${name.value}-${version.value}.jar",
    assembly/test := {},
    unmanagedBase := baseDirectory.value / ".." / "lib",
    nativeImageOptions += s"-H:ReflectionConfigurationFiles=${baseDirectory.value / ".." / "contrib" / "native-image-configs" / "reflect-config.json"}",
    nativeImageOptions += s"-H:ConfigurationFileDirectories=${baseDirectory.value / ".."  / "contrib" / "native-image-configs" }",
    nativeImageOptions +="-H:+JNI"
	).dependsOn(runtime)

