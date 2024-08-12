package leo.modules

import leo.datastructures.TPTP.Problem
import leo.modules.input.TPTPParser
import leo.modules.skolemizer.{ExistantialVariableDoesNotExistException, NotOnlyOneFormulaException, SingleFormulaSkolemizer}

import scala.io.Source
import java.io.{File, FileNotFoundException, PrintWriter}
import scala.collection.mutable

object ASkApp {
  final val name: String = "ask"
  final val version: String = "0.1.4"
  
  // Parameters of the invocation
  private[this] var param_inputFileName = ""
  private[this] var param_outputFileName: Option[String] = None
  private[this] var param_variableToSkolemize: Option[String] = None
  private[this] var param_skolemSymbolName: Option[String] = None
  private[this] var param_choiceTerm: Boolean = false
  // Internal state stuff
  private[this] var skolemizeAll: Boolean = true
  private[this] var skolemSymbolName: String = "aSk" // Default name
  private[this] var tstpOutput: Boolean = true

  final def main(args: Array[String]): Unit = {
    if (args.contains("--help")) {
      usage(); return
    }
    if (args.contains("--version")) {
      printVersion(); return
    }
    if (args.isEmpty) usage()
    else {
      var infile: Option[Source] = None
      var outfile: Option[PrintWriter] = None
      var error: Option[(String,String)] = None // TPTP status, error message

      try {
        parseArgs(args.toSeq)
        // Validate -s and -v arguments, if any
        param_variableToSkolemize match {
          case Some(_) =>
            skolemizeAll = false
          case None => // Nothing to do
        }

        param_skolemSymbolName match {
          case Some(value) =>
            if (value.endsWith("_NN") && value.length > 3 && skolemizeAll) {
              skolemSymbolName = value.reverse.replaceFirst("NN_", "d20%_").reverse
            } else {
              skolemSymbolName = value
              skolemizeAll = false
            }
          case None =>
          if (skolemizeAll) skolemSymbolName = skolemSymbolName + "_%02d"
        }

        // Allocate output file
        outfile = Some(if (param_outputFileName.isEmpty) new PrintWriter(System.out) else new PrintWriter(new File(param_outputFileName.get)))
        // Read input
        infile = Some(if (param_inputFileName == "-") io.Source.stdin else io.Source.fromFile(param_inputFileName))

        // Parse and select embedding
        val parsedInput = TPTPParser.problem(infile.get)
        val skolemized = new SingleFormulaSkolemizer(skolemSymbolName, skolemizeAll, param_variableToSkolemize, param_choiceTerm).apply(parsedInput)
        val result = generateResult(skolemized)
        // Write result
        outfile.get.print(result)
        outfile.get.flush()
        // Error handling
      } catch {
        case e: IllegalArgumentException =>
          error = if (e.getMessage == null) Some(("UsageError", e.toString)) else Some(("UsageError", e.getMessage))
          if (!tstpOutput) usage()
        case e: FileNotFoundException =>
          error = Some(("InputError", s"File cannot be found or is not readable/writable: ${e.getMessage}"))
        case _: NotOnlyOneFormulaException =>
          error = Some(("InputError", s"The input file contains more than one annotated formula. Aborting."))
        case _: ExistantialVariableDoesNotExistException =>
          error = Some(("UsageError", s"Existential variable does not exist."))
        case e: TPTPParser.TPTPParseException =>
          error = Some(("InputError", s"Input file could not be parsed, parse error at ${e.line}:${e.offset}: ${e.getMessage}"))
        case e: Throwable =>
          error = Some(("Error", s"Unexpected error: ${e.getMessage}. This is considered an implementation error, please report this!"))
      } finally {
        if (error.nonEmpty) {
          if (tstpOutput) {
            if (outfile.isDefined) {
              outfile.get.println(s"% SZS status ${error.get._1} for $param_inputFileName : ${error.get._2}\n")
              outfile.get.flush()
            } else println(s"% SZS status ${error.get._1} for $param_inputFileName : ${error.get._2}\n")
          } else {
            if (outfile.isDefined) {
              outfile.get.println(s"Error: ${error.get._2}")
              outfile.get.flush()
              if (param_outputFileName.isDefined) {
                if (param_outputFileName.get != "-") System.err.println(s"Error: ${error.get._2}")
              }
            } else println(s"Error: ${error.get._2}")
          }
        }
        try { infile.foreach(_.close())  } catch { case _:Throwable => () }
        try { outfile.foreach(_.close()) } catch { case _:Throwable => () }
        if (error.nonEmpty) System.exit(1)
      }
    }
  }



  private[this] final def generateResult(problem: Problem): String = {
    import java.util.Calendar

    val sb: mutable.StringBuilder = new mutable.StringBuilder()
    if (tstpOutput) sb.append(s"% SZS status Success for $param_inputFileName\n")
    sb.append(s"%%% This output was generated by $name, version $version\n")
    sb.append(s"%%% on ${Calendar.getInstance().getTime.toString}.\n")
    sb.append(s"%%% Options used:\n")
    sb.append(s"%%% -v: ${param_variableToSkolemize.getOrElse("<unset>")} -s: ${param_skolemSymbolName.getOrElse("<unset>")} \n")
    sb.append("\n")
    if (tstpOutput) sb.append(s"% SZS output start ListOfFormulae for $param_inputFileName\n")
    sb.append(problem.pretty)
    sb.append("\n")
    if (tstpOutput) sb.append(s"% SZS output end ListOfFormulae for $param_inputFileName\n")
    sb.toString()
  }

  private[this] final def printVersion(): Unit = {
    println(s"$name $version")
  }

  private[this] final def usage(): Unit = {
    println(s"usage: $name [OPTIONS] <file with one formula> [<output file>]")
    println(
      s"""
        | Apply a Skolemization transformation to the input file.
        | It is assumed that bound variables are named apart, and that there are no free variables.
        | <file with one formula> can be either a file name or '-' (without parentheses) for stdin.
        | If <output file> is specified, write result to <output file>, otherwise to stdout.
        |
        | If no options are provided, all the existentials in the formula are Skolemized,
        | using some fixed symbol suffixed with _NN, NN=00-99.
        | If only -s is provided and <Skolem symbol to use> is of the form
        | <something>_NN, Skolemize all the existentials in the formula, using
        | the symbol <something> replacing NN with 00-99.
        | If only -s is provided and <Skolem symbol to use> is not of the form
        | <something>_NN, Skolemize the leftmost existentially quantified variable
        | in the formula, using the <Skolem symbol to use>.
        | If only -v is provided, Skolemize the <variable to Skolemize>, using
        | some fixed symbol suffixed with _00.
        | If both -s and -v are provided, Skolemize the <variable to Skolemize> using
        | the symbol <Skolem symbol to use>.
        | If -e is specified, also output the equality between the Skolem term and
        |   an epsilon term.
        |
        | Options:
        |  -v <variable to Skolemize>
        |     The existential variable to Skolemize.
        |
        |  -s <Skolem symbol to use>
        |     The Skolem symbol base name to use for the Skolemization symbols.
        |     Defaults to "aSk" if omitted.
        |
        |  -e Output a choice term for the Skolem term.
        |
        |  --no-tstp
        |     Disable TSTP-compatible output: The output in <output file> (or stdout) will
        |     not start with a SZS status value and the output will not be wrapped within
        |     SZS BEGIN and SZS END block delimiters.
        |
        |  --version
        |     Prints the version number of the executable and terminates.
        |
        |  --help
        |     Prints this description and terminates.
        |""".stripMargin)
  }

  private[this] final def parseArgs(args: Seq[String]): Unit = {
    var args0 = args
    while (args0.nonEmpty) {
      args0 match {
        case Seq("-v", variable, rest@_*) =>
          args0 = rest
          param_variableToSkolemize = Some(variable)
        case Seq("-s", skolemName, rest@_*) =>
          args0 = rest
          param_skolemSymbolName = Some(skolemName)
        case Seq("-e", rest@_*) =>
          args0 = rest
          param_choiceTerm = true
        case Seq("--no-tstp", rest@_*) =>
          args0 = rest
          tstpOutput = false
        case Seq(f) =>
          args0 = Seq.empty
          param_inputFileName = f
        case Seq(f, o) =>
          args0 = Seq.empty
          param_inputFileName = f
          param_outputFileName = Some(o)
        case _ => throw new IllegalArgumentException("Unrecognized arguments.")
      }
    }
  }


}
