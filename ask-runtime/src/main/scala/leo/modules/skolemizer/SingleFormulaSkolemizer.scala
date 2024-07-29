package leo.modules.skolemizer

import leo.datastructures.TPTP
import leo.datastructures.TPTP.{FOF, TFF}

final class SingleFormulaSkolemizer(skolemizationSymbol: String, skolemizeAll: Boolean, variableToSkolemize: Option[String]) {
  //////////////////////////////////////////////////////////////////////////////
  // general stuff
  //////////////////////////////////////////////////////////////////////////////

  private[this] var nextSkolemIndex: Int = 0
  private def freshSkolemSymbol(): String = {
    val nextSkolemIndexFormatted: String = "%02d".format(nextSkolemIndex)
    nextSkolemIndex = nextSkolemIndex + 1
    s"${skolemizationSymbol}_$nextSkolemIndexFormatted"
  }

  private[this] var typeDeclarationsOfIntroducedSkolemSymbols: Seq[TPTP.AnnotatedFormula] = Seq.empty

  def apply(problem: TPTP.Problem): TPTP.Problem = {
    val (_, nonTypeFormulas) = problem.formulas.partition(_.role == "type")
    if (nonTypeFormulas.size < 1) problem
    else if (nonTypeFormulas.size > 1) throw new NotOnlyOneFormulaException
    else {
      val skolemized = apply(nonTypeFormulas.head)
      val extraTypeDeclarations: Seq[TPTP.AnnotatedFormula] = typeDeclarationsOfIntroducedSkolemSymbols
      val extraDefinitions: Seq[TPTP.AnnotatedFormula] = Seq() // TODO
      TPTP.Problem(problem.includes, extraTypeDeclarations ++ extraDefinitions :+ skolemized, problem.formulaComments)
    }
  }

  private def apply(formula: TPTP.AnnotatedFormula): TPTP.AnnotatedFormula = {
    // Oh boy ...
    val inferenceTerm: TPTP.GeneralTerm =
      TPTP.GeneralTerm(
        Seq(
          TPTP.MetaFunctionData("inferred",
            Seq(
              TPTP.GeneralTerm(
                Seq(TPTP.MetaFunctionData("skolemization", Seq.empty)),
                None
              ),
              TPTP.GeneralTerm(
                Seq.empty,
                Some(
                  Seq(
                    TPTP.GeneralTerm(
                      Seq(TPTP.MetaFunctionData("status", Seq(TPTP.GeneralTerm(Seq(TPTP.MetaFunctionData("esa", Seq.empty)),None)))),
                      None
                    )
                  )
                )
              )
            )
          )
        ), None)
    val annotation: TPTP.Annotations = Some((inferenceTerm, None))

    formula match {
      case TPTP.THFAnnotated(name, _, formula, _) =>
        TPTP.THFAnnotated(s"${name}_skolemized", "plain", skolemizeTHF(formula), annotation)
      case TPTP.TFFAnnotated(name, _, formula, _) =>
        TPTP.TFFAnnotated(s"${name}_skolemized", "plain", skolemizeTFF(formula), annotation)
      case TPTP.FOFAnnotated(name, _, formula, _) =>
        TPTP.FOFAnnotated(s"${name}_skolemized", "plain", skolemizeFOF(formula), annotation)
      case _ => formula
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // FOF stuff
  //////////////////////////////////////////////////////////////////////////////

  private def skolemizeFOF(statement: TPTP.FOF.Statement): TPTP.FOF.Statement = {
    statement match {
      case FOF.Logical(formula) => FOF.Logical(skolemizeFOFFormula(formula))
    }
  }
  private def skolemizeFOFFormula(formula: TPTP.FOF.Formula): TPTP.FOF.Formula = skolemizeFOFFormula0(formula, polarity = true, univVars = Seq.empty)
  private def skolemizeFOFFormula0(formula: TPTP.FOF.Formula, polarity: Boolean, univVars: Seq[String]): TPTP.FOF.Formula = {
    formula match {
      // Act cases
      case FOF.QuantifiedFormula(quantifier, variableList, body) if quantifier == TPTP.FOF.? && polarity =>
        skolemizeFOFFormula1(quantifier, variableList, body, polarity, univVars)
      case FOF.QuantifiedFormula(quantifier, variableList, body) if quantifier == TPTP.FOF.! && !polarity =>
        skolemizeFOFFormula1(quantifier, variableList, body, polarity, univVars)
      // recursive cases with polarity switch
      /* the remaining quantifier cases are ! with positive polarity and ? with negative polarity, both are Skolem dependency variable cases for the recursion */
      case FOF.QuantifiedFormula(quantifier, variableList, body) =>
        FOF.QuantifiedFormula(quantifier, variableList, skolemizeFOFFormula0(body, polarity, univVars ++ variableList))
      case FOF.UnaryFormula(connective, body) => // change polarity
        connective match {
          case FOF.~ => FOF.UnaryFormula(connective, skolemizeFOFFormula0(body, !polarity, univVars))
        }
      case FOF.BinaryFormula(connective, left, right) => // change polarity for =>
        connective match {
          case FOF.<=> =>
            if (skolemizeAll || variableToSkolemize.isDefined)
              FOF.BinaryFormula(FOF.&,
                FOF.BinaryFormula(FOF.Impl, skolemizeFOFFormula0(left, !polarity, univVars), skolemizeFOFFormula0(right, polarity, univVars)),
                FOF.BinaryFormula(FOF.<=, skolemizeFOFFormula0(left, polarity, univVars),skolemizeFOFFormula0(right, !polarity, univVars))
              )
            else
              FOF.BinaryFormula(FOF.&,
                FOF.BinaryFormula(FOF.Impl, skolemizeFOFFormula0(left, !polarity, univVars), right),
                FOF.BinaryFormula(FOF.<=, skolemizeFOFFormula0(left, polarity, univVars), right)
              )
          case FOF.<~> =>
            if (skolemizeAll || variableToSkolemize.isDefined)
              FOF.BinaryFormula(FOF.~&,
                FOF.BinaryFormula(FOF.Impl, skolemizeFOFFormula0(left, polarity, univVars), skolemizeFOFFormula0(right, !polarity, univVars)),
                FOF.BinaryFormula(FOF.<=, skolemizeFOFFormula0(left, !polarity, univVars),skolemizeFOFFormula0(right, polarity, univVars))
              )
            else
              FOF.BinaryFormula(FOF.~&,
                FOF.BinaryFormula(FOF.Impl, skolemizeFOFFormula0(left, polarity, univVars), right),
                FOF.BinaryFormula(FOF.<=, skolemizeFOFFormula0(left, !polarity, univVars), right)
              )
          case FOF.Impl =>
            if (skolemizeAll || variableToSkolemize.isDefined) FOF.BinaryFormula(connective, skolemizeFOFFormula0(left, !polarity, univVars), skolemizeFOFFormula0(right, polarity, univVars))
            else FOF.BinaryFormula(connective, skolemizeFOFFormula0(left, !polarity, univVars), right)
          case FOF.<= =>
            if (skolemizeAll || variableToSkolemize.isDefined) FOF.BinaryFormula(connective, skolemizeFOFFormula0(left, polarity, univVars), skolemizeFOFFormula0(right, !polarity, univVars))
            else FOF.BinaryFormula(connective, skolemizeFOFFormula0(left, polarity, univVars), right)
          case FOF.~| | FOF.~& =>
            if (skolemizeAll || variableToSkolemize.isDefined) FOF.BinaryFormula(connective, skolemizeFOFFormula0(left, !polarity, univVars), skolemizeFOFFormula0(right, !polarity, univVars))
            else FOF.BinaryFormula(connective, skolemizeFOFFormula0(left, !polarity, univVars), right)
          case FOF.| | FOF.& =>
            if (skolemizeAll || variableToSkolemize.isDefined) FOF.BinaryFormula(connective, skolemizeFOFFormula0(left, polarity, univVars), skolemizeFOFFormula0(right, polarity, univVars))
            else FOF.BinaryFormula(connective, skolemizeFOFFormula0(left, polarity, univVars), right)
        }
      case _ => formula
    }
  }

  private def skolemizeFOFFormula1(quantifier: FOF.Quantifier, variableList: Seq[String], body: FOF.Formula, polarity: Boolean, univVars: Seq[String]): FOF.Formula =
    // if name check name (and recurse if no, and yes if yes), if no name do it and then return, otherwise
    variableToSkolemize match {
      case Some(variableName) =>
        // just skolemize that one
        if (variableList.contains(variableName)) {
          val idxOfVariable = variableList.indexOf(variableName)
          val (before, after0) = variableList.splitAt(idxOfVariable)
          val theVariable = after0.head
          val after = after0.tail
          val skolemized = skolemizeFOFFormula2(body, theVariable, univVars)
          val rest = before ++ after
          if (rest.nonEmpty)  FOF.QuantifiedFormula(quantifier, before ++ after, skolemized)
          else skolemized
        } else /* recurse */ FOF.QuantifiedFormula(quantifier, variableList, skolemizeFOFFormula0(body, polarity, univVars))
      case None =>
        if (skolemizeAll) {
          val skolemized = variableList.foldLeft(body) { case (acc, variable) => skolemizeFOFFormula2(acc, variable, univVars) }
          skolemizeFOFFormula0(skolemized, polarity, univVars)
        } else {
          // only first occurrence and then return
          val theVariable = variableList.head
          val after = variableList.tail
          val skolemized = skolemizeFOFFormula2(body, theVariable, univVars)
          if (after.nonEmpty) FOF.QuantifiedFormula(quantifier, after, skolemized)
          else skolemized
        }
    }
  private def skolemizeFOFFormula2(formula: FOF.Formula, variableToSkolemize: String, universalVars: Seq[String]): FOF.Formula = {
    val skolemSymbol: String = freshSkolemSymbol()
    val skolemTerm: FOF.Term = FOF.AtomicTerm(skolemSymbol, universalVars.map(FOF.Variable))
    replaceEveryVarOccurrenceWithTermFOF(formula, FOF.Variable(variableToSkolemize), skolemTerm)
  }
  private def replaceEveryVarOccurrenceWithTermFOF(formula: TPTP.FOF.Formula, variable: TPTP.FOF.Variable, term: TPTP.FOF.Term): FOF.Formula = {
    formula match {
      case FOF.AtomicFormula(f, args) =>
        FOF.AtomicFormula(f, args.map(replaceEveryVarOccurrenceWithTermFOF(_, variable, term)))
      case FOF.QuantifiedFormula(quantifier, variableList, body) =>
        FOF.QuantifiedFormula(quantifier, variableList, replaceEveryVarOccurrenceWithTermFOF(body, variable, term))
      case FOF.UnaryFormula(connective, body) =>
        FOF.UnaryFormula(connective, replaceEveryVarOccurrenceWithTermFOF(body, variable, term))
      case FOF.BinaryFormula(connective, left, right) =>
        FOF.BinaryFormula(connective, replaceEveryVarOccurrenceWithTermFOF(left, variable, term), replaceEveryVarOccurrenceWithTermFOF(right, variable, term))
      case FOF.Equality(left, right) =>
        FOF.Equality(replaceEveryVarOccurrenceWithTermFOF(left, variable, term), replaceEveryVarOccurrenceWithTermFOF(right, variable, term))
      case FOF.Inequality(left, right) =>
        FOF.Inequality(replaceEveryVarOccurrenceWithTermFOF(left, variable, term), replaceEveryVarOccurrenceWithTermFOF(right, variable, term))
    }
  }
  private def replaceEveryVarOccurrenceWithTermFOF(term: TPTP.FOF.Term, variable: TPTP.FOF.Variable, replacement: TPTP.FOF.Term): FOF.Term = {
    term match {
      case FOF.AtomicTerm(f, args) =>
        FOF.AtomicTerm(f, args.map(replaceEveryVarOccurrenceWithTermFOF(_, variable, replacement)))
      case FOF.Variable(name) =>
        if (name == variable.name) replacement
        else term
      case _ => term
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // TFF stuff
  //////////////////////////////////////////////////////////////////////////////

  private def skolemizeTFF(statement: TPTP.TFF.Statement): TPTP.TFF.Statement = {
    statement match {
      case TFF.Logical(formula) => TFF.Logical(skolemizeTFFFormula(formula))
      case _ => statement
    }
  }

  private def skolemizeTFFFormula(formula: TPTP.TFF.Formula): TPTP.TFF.Formula =
    skolemizeTFFFormula0(formula, polarity = true, univVars = Seq.empty)
  private def skolemizeTFFFormula0(formula: TPTP.TFF.Formula, polarity: Boolean, univVars: Seq[TFF.TypedVariable]): TPTP.TFF.Formula = {
    formula match {
      // Act cases
      case TFF.QuantifiedFormula(quantifier, variableList, body) if quantifier == TPTP.TFF.? && polarity =>
        skolemizeTFFFormula1(quantifier, variableList, body, polarity, univVars)
      case TFF.QuantifiedFormula(quantifier, variableList, body) if quantifier == TPTP.TFF.! && !polarity =>
        skolemizeTFFFormula1(quantifier, variableList, body, polarity, univVars)
      // recursive cases with polarity switch
      /* the remaining quantifier cases are ! with positive polarity and ? with negative polarity, both are Skolem dependency variable cases for the recursion */
      case TFF.QuantifiedFormula(quantifier, variableList, body) =>
        TFF.QuantifiedFormula(quantifier, variableList, skolemizeTFFFormula0(body, polarity, univVars ++ variableList))
      case TFF.UnaryFormula(connective, body) => // change polarity
        connective match {
          case TFF.~ => TFF.UnaryFormula(connective, skolemizeTFFFormula0(body, !polarity, univVars))
        }
      case TFF.BinaryFormula(connective, left, right) => // change polarity for =>
        connective match {
          case TFF.<=> =>
            if (skolemizeAll || variableToSkolemize.isDefined)
              TFF.BinaryFormula(TFF.&,
                TFF.BinaryFormula(TFF.Impl, skolemizeTFFFormula0(left, !polarity, univVars), skolemizeTFFFormula0(right, polarity, univVars)),
                TFF.BinaryFormula(TFF.<=, skolemizeTFFFormula0(left, polarity, univVars),skolemizeTFFFormula0(right, !polarity, univVars))
              )
            else
              TFF.BinaryFormula(TFF.&,
                TFF.BinaryFormula(TFF.Impl, skolemizeTFFFormula0(left, !polarity, univVars), right),
                TFF.BinaryFormula(TFF.<=, skolemizeTFFFormula0(left, polarity, univVars), right)
              )
          case TFF.<~> =>
            if (skolemizeAll || variableToSkolemize.isDefined)
              TFF.BinaryFormula(TFF.~&,
                TFF.BinaryFormula(TFF.Impl, skolemizeTFFFormula0(left, polarity, univVars), skolemizeTFFFormula0(right, !polarity, univVars)),
                TFF.BinaryFormula(TFF.<=, skolemizeTFFFormula0(left, !polarity, univVars),skolemizeTFFFormula0(right, polarity, univVars))
              )
            else
              TFF.BinaryFormula(TFF.~&,
                TFF.BinaryFormula(TFF.Impl, skolemizeTFFFormula0(left, polarity, univVars), right),
                TFF.BinaryFormula(TFF.<=, skolemizeTFFFormula0(left, !polarity, univVars), right)
              )
          case TFF.Impl =>
            if (skolemizeAll || variableToSkolemize.isDefined) TFF.BinaryFormula(connective, skolemizeTFFFormula0(left, !polarity, univVars), skolemizeTFFFormula0(right, polarity, univVars))
            else TFF.BinaryFormula(connective, skolemizeTFFFormula0(left, !polarity, univVars), right)
          case TFF.<= =>
            if (skolemizeAll || variableToSkolemize.isDefined) TFF.BinaryFormula(connective, skolemizeTFFFormula0(left, polarity, univVars), skolemizeTFFFormula0(right, !polarity, univVars))
            else TFF.BinaryFormula(connective, skolemizeTFFFormula0(left, polarity, univVars), right)
          case TFF.~| | TFF.~& =>
            if (skolemizeAll || variableToSkolemize.isDefined) TFF.BinaryFormula(connective, skolemizeTFFFormula0(left, !polarity, univVars), skolemizeTFFFormula0(right, !polarity, univVars))
            else TFF.BinaryFormula(connective, skolemizeTFFFormula0(left, !polarity, univVars), right)
          case TFF.| | TFF.& =>
            if (skolemizeAll || variableToSkolemize.isDefined) TFF.BinaryFormula(connective, skolemizeTFFFormula0(left, polarity, univVars), skolemizeTFFFormula0(right, polarity, univVars))
            else TFF.BinaryFormula(connective, skolemizeTFFFormula0(left, polarity, univVars), right)
        }
      case TFF.ConditionalFormula(condition, thn, els) =>
        TFF.ConditionalFormula(skolemizeTFFFormula0(condition, !polarity, univVars), thn, els)
      case TFF.NonclassicalPolyaryFormula(connective, args) =>
        TFF.NonclassicalPolyaryFormula(connective, args.map(x => skolemizeTFFFormula0(x, polarity, univVars)))

      /*case TFF.LetFormula(typing, binding, body) => ???
      case TFF.FormulaVariable(name) => ???
      case TFF.Assignment(lhs, rhs) => ???
      case TFF.MetaIdentity(lhs, rhs) => ??? */

      case _ => formula
    }
  }

  private def skolemizeTFFFormula1(quantifier: TFF.Quantifier, variableList: Seq[TFF.TypedVariable],
                                   body: TFF.Formula, polarity: Boolean, univVars: Seq[TFF.TypedVariable]): TFF.Formula = {
    // if name check name (and recurse if no, and yes if yes), if no name do it and then return, otherwise
    variableToSkolemize match {
      case Some(variableName) =>
        // just skolemize that one
        if (variableList.exists(_._1 == variableName)) {
          val idxOfVariable = variableList.indexWhere(_._1 == variableName)
          val (before, after0) = variableList.splitAt(idxOfVariable)
          val theVariable = after0.head
          val after = after0.tail
          val skolemized = skolemizeTFFFormula2(body, theVariable, univVars)
          val rest = before ++ after
          if (rest.nonEmpty)  TFF.QuantifiedFormula(quantifier, before ++ after, skolemized)
          else skolemized
        } else /* recurse */ TFF.QuantifiedFormula(quantifier, variableList, skolemizeTFFFormula0(body, polarity, univVars))
      case None =>
        if (skolemizeAll) {
          val skolemized = variableList.foldLeft(body) { case (acc, variable) => skolemizeTFFFormula2(acc, variable, univVars) }
          skolemizeTFFFormula0(skolemized, polarity, univVars)
        } else {
          // only first occurrence and then return
          val theVariable = variableList.head
          val after = variableList.tail
          val skolemized = skolemizeTFFFormula2(body, theVariable, univVars)
          if (after.nonEmpty) TFF.QuantifiedFormula(quantifier, after, skolemized)
          else skolemized
        }
    }
  }
  private def skolemizeTFFFormula2(formula: TFF.Formula, variableToSkolemize: TFF.TypedVariable, universalVars: Seq[TFF.TypedVariable]): TFF.Formula = {
    val skolemSymbol: String = freshSkolemSymbol()
    val goalTypeOfSkolemSymbol = variableToSkolemize._2 match {
      case Some(ty) => ty
      case None => TFF.AtomicType("$i", Seq.empty)
    }
    val typesOfDependencies = universalVars.map { case (_, ty) =>
      ty match {
        case Some(ty0) => ty0
        case None => TFF.AtomicType("$i", Seq.empty)
      }
    }
    val typeOfSkolemSymbol: TFF.Type = TFF.MappingType(typesOfDependencies, goalTypeOfSkolemSymbol)
    val typeDeclaration: TPTP.TFFAnnotated = TPTP.TFFAnnotated(
      s"${skolemSymbol}_decl",
      "type",
      TFF.Typing(skolemSymbol, typeOfSkolemSymbol),
      None)
    typeDeclarationsOfIntroducedSkolemSymbols = typeDeclarationsOfIntroducedSkolemSymbols :+ typeDeclaration

    val skolemTerm: TFF.Term = TFF.AtomicTerm(skolemSymbol, universalVars.map { case (name, _) => TFF.Variable(name) })
    replaceEveryVarOccurrenceWithTermTFF(formula, variableToSkolemize, skolemTerm)
  }

  private def replaceEveryVarOccurrenceWithTermTFF(formula: TPTP.TFF.Formula, variable: TFF.TypedVariable, term: TPTP.TFF.Term): TFF.Formula = {
    formula match {
      case TFF.AtomicFormula(f, args) =>
        TFF.AtomicFormula(f, args.map(replaceEveryVarOccurrenceWithTermTFF(_, variable, term)))
      case TFF.QuantifiedFormula(quantifier, variableList, body) =>
        TFF.QuantifiedFormula(quantifier, variableList, replaceEveryVarOccurrenceWithTermTFF(body, variable, term))
      case TFF.UnaryFormula(connective, body) =>
        TFF.UnaryFormula(connective, replaceEveryVarOccurrenceWithTermTFF(body, variable, term))
      case TFF.BinaryFormula(connective, left, right) =>
        TFF.BinaryFormula(connective, replaceEveryVarOccurrenceWithTermTFF(left, variable, term), replaceEveryVarOccurrenceWithTermTFF(right, variable, term))
      case TFF.Equality(left, right) =>
        TFF.Equality(replaceEveryVarOccurrenceWithTermTFF(left, variable, term), replaceEveryVarOccurrenceWithTermTFF(right, variable, term))
      case TFF.Inequality(left, right) =>
        TFF.Inequality(replaceEveryVarOccurrenceWithTermTFF(left, variable, term), replaceEveryVarOccurrenceWithTermTFF(right, variable, term))
      case TFF.FormulaVariable(name) =>
        if (name == variable._1) {
          term match {
            case TFF.AtomicTerm(f, args) => TFF.AtomicFormula(f, args)
            case _ => formula // other cases should not occur
          }
        } else formula
      case TFF.NonclassicalPolyaryFormula(connective, args) =>
        TFF.NonclassicalPolyaryFormula(connective, args.map(replaceEveryVarOccurrenceWithTermTFF(_, variable, term)))
      case TFF.ConditionalFormula(condition, thn, els) =>
        TFF.ConditionalFormula(replaceEveryVarOccurrenceWithTermTFF(condition, variable, term),
          replaceEveryVarOccurrenceWithTermTFF(thn, variable, term),
          replaceEveryVarOccurrenceWithTermTFF(els, variable, term))
      case TFF.LetFormula(typing, binding, body) =>
        TFF.LetFormula(typing,
          binding.map {case (l,r) => (l, replaceEveryVarOccurrenceWithTermTFF(r, variable, term))},
          replaceEveryVarOccurrenceWithTermTFF(body, variable, term)
        )
      case _ => formula
    }
  }
  private def replaceEveryVarOccurrenceWithTermTFF(term: TPTP.TFF.Term, variable: TFF.TypedVariable, replacement: TPTP.TFF.Term): TFF.Term = {
    term match {
      case TFF.AtomicTerm(f, args) =>
        TFF.AtomicTerm(f, args.map(replaceEveryVarOccurrenceWithTermTFF(_, variable, replacement)))
      case TFF.Variable(name) =>
        if (name == variable._1) replacement
        else term
      case TFF.Tuple(elements) => TFF.Tuple(elements.map(replaceEveryVarOccurrenceWithTermTFF(_, variable, replacement)))
      case TFF.FormulaTerm(formula) => TFF.FormulaTerm(replaceEveryVarOccurrenceWithTermTFF(formula, variable, replacement))
      case _ => term
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // THF stuff
  //////////////////////////////////////////////////////////////////////////////
  private def skolemizeTHF(statement: TPTP.THF.Statement): TPTP.THF.Statement = ???
}
