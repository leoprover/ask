package leo.modules.skolemizer

import leo.datastructures.TPTP
import leo.datastructures.TPTP.{FOF, TFF, THF}

final class SingleFormulaSkolemizer(skolemizationSymbol: String,
                                    skolemizeAll: Boolean,
                                    variableToSkolemize: Option[String],
                                    choiceTerms: Boolean) {
  //////////////////////////////////////////////////////////////////////////////
  // general stuff
  //////////////////////////////////////////////////////////////////////////////

  private[this] var nextSkolemIndex: Int = 0
  private def freshSkolemSymbol(): String = {
    val result = s"$skolemizationSymbol".format(nextSkolemIndex)
    nextSkolemIndex = nextSkolemIndex + 1
    result
  }

  /* Map: Variable -> skolem symbol */
  private[this] var introducedSkolemSymbols: Map[String,String] = Map.empty
  private[this] var introducedSkolemTerms: Map[String,String] = Map.empty
  private[this] var typeDeclarationsOfIntroducedSkolemSymbols: Seq[TPTP.AnnotatedFormula] = Seq.empty
  private[this] var epsilonTermAxioms: Seq[TPTP.AnnotatedFormula] = Seq.empty

  /* If Skolemizing only one variable: did the variable occur? */
  private[this] var variableExists: Boolean = false

  def apply(problem: TPTP.Problem): TPTP.Problem = {
    val (_, nonTypeFormulas) = problem.formulas.partition(_.role == "type")
    if (nonTypeFormulas.size < 1) problem
    else if (nonTypeFormulas.size > 1) throw new NotOnlyOneFormulaException
    else {
      val skolemized = apply(nonTypeFormulas.head)
      val extraTypeDeclarations: Seq[TPTP.AnnotatedFormula] = typeDeclarationsOfIntroducedSkolemSymbols
      val extraDefinitions: Seq[TPTP.AnnotatedFormula] = epsilonTermAxioms
      if (variableToSkolemize.isDefined && !variableExists) throw new ExistantialVariableDoesNotExistException()
      TPTP.Problem(problem.includes, extraTypeDeclarations ++ extraDefinitions :+ skolemized, problem.formulaComments)
    }
  }

  private def apply(formula: TPTP.AnnotatedFormula): TPTP.AnnotatedFormula = {
    val suffix = "_ASked"

    formula match {
      case TPTP.THFAnnotated(name, role, formula0, _) =>
        TPTP.THFAnnotated(s"$name$suffix", role, skolemizeTHF(name, formula0), assumptionAnnotation(formula))
      case TPTP.TFFAnnotated(name, role, formula0, _) =>
        TPTP.TFFAnnotated(s"$name$suffix", role, skolemizeTFF(name, formula0), assumptionAnnotation(formula))
      case TPTP.FOFAnnotated(name, role, formula0, _) =>
        TPTP.FOFAnnotated(s"$name$suffix", role, skolemizeFOF(name, formula0), assumptionAnnotation(formula))
      case _ => formula
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // FOF stuff
  //////////////////////////////////////////////////////////////////////////////

  private def skolemizeFOF(name: String, statement: TPTP.FOF.Statement): TPTP.FOF.Statement = {
    statement match {
      case FOF.Logical(formula) => FOF.Logical(skolemizeFOFFormula(name, formula))
    }
  }
  private def skolemizeFOFFormula(name: String, formula: TPTP.FOF.Formula): TPTP.FOF.Formula = skolemizeFOFFormula0(name, formula, polarity = true, univVars = Seq.empty)
  private def skolemizeFOFFormula0(name: String, formula: TPTP.FOF.Formula, polarity: Boolean, univVars: Seq[String]): TPTP.FOF.Formula = {
    formula match {
      // Act cases
      case FOF.QuantifiedFormula(quantifier, variableList, body) if quantifier == TPTP.FOF.? && polarity =>
        skolemizeFOFFormula1(name, quantifier, variableList, body, polarity, univVars)
      case FOF.QuantifiedFormula(quantifier, variableList, body) if quantifier == TPTP.FOF.! && !polarity =>
        skolemizeFOFFormula1(name, quantifier, variableList, body, polarity, univVars)
      // recursive cases with polarity switch
      /* the remaining quantifier cases are ! with positive polarity and ? with negative polarity, both are Skolem dependency variable cases for the recursion */
      case FOF.QuantifiedFormula(quantifier, variableList, body) =>
        FOF.QuantifiedFormula(quantifier, variableList, skolemizeFOFFormula0(name, body, polarity, univVars ++ variableList))
      case FOF.UnaryFormula(connective, body) => // change polarity
        connective match {
          case FOF.~ => FOF.UnaryFormula(connective, skolemizeFOFFormula0(name, body, !polarity, univVars))
        }
      case FOF.BinaryFormula(connective, left, right) => // change polarity for =>
        connective match {
          case FOF.<=> =>
            if (skolemizeAll || variableToSkolemize.isDefined)
              FOF.BinaryFormula(FOF.&,
                FOF.BinaryFormula(FOF.Impl, skolemizeFOFFormula0(name, left, !polarity, univVars), skolemizeFOFFormula0(name, right, polarity, univVars)),
                FOF.BinaryFormula(FOF.<=, skolemizeFOFFormula0(name, left, polarity, univVars),skolemizeFOFFormula0(name, right, !polarity, univVars))
              )
            else
              FOF.BinaryFormula(FOF.&,
                FOF.BinaryFormula(FOF.Impl, skolemizeFOFFormula0(name, left, !polarity, univVars), right),
                FOF.BinaryFormula(FOF.<=, skolemizeFOFFormula0(name, left, polarity, univVars), right)
              )
          case FOF.<~> =>
            if (skolemizeAll || variableToSkolemize.isDefined)
              FOF.BinaryFormula(FOF.~&,
                FOF.BinaryFormula(FOF.Impl, skolemizeFOFFormula0(name, left, polarity, univVars), skolemizeFOFFormula0(name, right, !polarity, univVars)),
                FOF.BinaryFormula(FOF.<=, skolemizeFOFFormula0(name, left, !polarity, univVars),skolemizeFOFFormula0(name, right, polarity, univVars))
              )
            else
              FOF.BinaryFormula(FOF.~&,
                FOF.BinaryFormula(FOF.Impl, skolemizeFOFFormula0(name, left, polarity, univVars), right),
                FOF.BinaryFormula(FOF.<=, skolemizeFOFFormula0(name, left, !polarity, univVars), right)
              )
          case FOF.Impl =>
            if (skolemizeAll || variableToSkolemize.isDefined) FOF.BinaryFormula(connective, skolemizeFOFFormula0(name, left, !polarity, univVars), skolemizeFOFFormula0(name, right, polarity, univVars))
            else FOF.BinaryFormula(connective, skolemizeFOFFormula0(name, left, !polarity, univVars), right)
          case FOF.<= =>
            if (skolemizeAll || variableToSkolemize.isDefined) FOF.BinaryFormula(connective, skolemizeFOFFormula0(name, left, polarity, univVars), skolemizeFOFFormula0(name, right, !polarity, univVars))
            else FOF.BinaryFormula(connective, skolemizeFOFFormula0(name, left, polarity, univVars), right)
          case FOF.~| | FOF.~& =>
            if (skolemizeAll || variableToSkolemize.isDefined) FOF.BinaryFormula(connective, skolemizeFOFFormula0(name, left, !polarity, univVars), skolemizeFOFFormula0(name, right, !polarity, univVars))
            else FOF.BinaryFormula(connective, skolemizeFOFFormula0(name, left, !polarity, univVars), right)
          case FOF.| | FOF.& =>
            if (skolemizeAll || variableToSkolemize.isDefined) FOF.BinaryFormula(connective, skolemizeFOFFormula0(name, left, polarity, univVars), skolemizeFOFFormula0(name, right, polarity, univVars))
            else FOF.BinaryFormula(connective, skolemizeFOFFormula0(name, left, polarity, univVars), right)
        }
      case _ => formula
    }
  }

  private def skolemizeFOFFormula1(name: String, quantifier: FOF.Quantifier, variableList: Seq[String], body: FOF.Formula, polarity: Boolean, univVars: Seq[String]): FOF.Formula =
    // if name check name (and recurse if no, and yes if yes), if no name do it and then return, otherwise
    variableToSkolemize match {
      case Some(variableName) =>
        // just skolemize that one
        if (variableList.contains(variableName)) {
          variableExists = true
          val idxOfVariable = variableList.indexOf(variableName)
          val (before, after0) = variableList.splitAt(idxOfVariable)
          val theVariable = after0.head
          val after = after0.tail
          val skolemized = skolemizeFOFFormula2(name, body, theVariable, univVars)
          val rest = before ++ after
          if (rest.nonEmpty)  FOF.QuantifiedFormula(quantifier, before ++ after, skolemized)
          else skolemized
        } else /* recurse */ FOF.QuantifiedFormula(quantifier, variableList, skolemizeFOFFormula0(name, body, polarity, univVars))
      case None =>
        if (skolemizeAll) {
          val skolemized = variableList.foldLeft(body) { case (acc, variable) => skolemizeFOFFormula2(name, acc, variable, univVars) }
          skolemizeFOFFormula0(name, skolemized, polarity, univVars)
        } else {
          // only first occurrence and then return
          val theVariable = variableList.head
          val after = variableList.tail
          val skolemized = skolemizeFOFFormula2(name, body, theVariable, univVars)
          if (after.nonEmpty) FOF.QuantifiedFormula(quantifier, after, skolemized)
          else skolemized
        }
    }
  private def skolemizeFOFFormula2(name: String, formula: FOF.Formula, variableToSkolemize: String, universalVars: Seq[String]): FOF.Formula = {
    val skolemSymbol: String = freshSkolemSymbol()
    val skolemTerm: FOF.Term = FOF.AtomicTerm(skolemSymbol, universalVars.map(FOF.Variable))
    val skolemTermAsTFF = leo.modules.tptputils.SyntaxTransform.fofTermToTFF(skolemTerm)
    val formulaAsTFF = leo.modules.tptputils.SyntaxTransform.fofLogicFormulaToTFF(formula)
    introducedSkolemSymbols = introducedSkolemSymbols + (variableToSkolemize -> skolemSymbol)
    introducedSkolemTerms = introducedSkolemTerms + (variableToSkolemize -> skolemTermAsTFF.pretty)
    if (choiceTerms) epsilonTermAxioms = epsilonTermAxioms :+ generateEpsilonTermTFF(name,
      skolemSymbol,
      skolemTermAsTFF,
      (variableToSkolemize, Some(TFF.AtomicType("$i", Seq.empty))),
      universalVars.map(vari => (vari, Some(TFF.AtomicType("$i", Seq.empty)))),
      formulaAsTFF)
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

  private def skolemizeTFF(name: String, statement: TPTP.TFF.Statement): TPTP.TFF.Statement = {
    statement match {
      case TFF.Logical(formula) => TFF.Logical(skolemizeTFFFormula(name,formula))
      case _ => statement
    }
  }

  private def skolemizeTFFFormula(name: String, formula: TPTP.TFF.Formula): TPTP.TFF.Formula =
    skolemizeTFFFormula0(name, formula, polarity = true, univVars = Seq.empty)
  private def skolemizeTFFFormula0(name: String, formula: TPTP.TFF.Formula, polarity: Boolean, univVars: Seq[TFF.TypedVariable]): TPTP.TFF.Formula = {
    formula match {
      // Act cases
      case TFF.QuantifiedFormula(quantifier, variableList, body) if quantifier == TPTP.TFF.? && polarity =>
        skolemizeTFFFormula1(name, quantifier, variableList, body, polarity, univVars)
      case TFF.QuantifiedFormula(quantifier, variableList, body) if quantifier == TPTP.TFF.! && !polarity =>
        skolemizeTFFFormula1(name, quantifier, variableList, body, polarity, univVars)
      // recursive cases with polarity switch
      /* the remaining quantifier cases are ! with positive polarity and ? with negative polarity, both are Skolem dependency variable cases for the recursion */
      case TFF.QuantifiedFormula(quantifier, variableList, body) =>
        TFF.QuantifiedFormula(quantifier, variableList, skolemizeTFFFormula0(name, body, polarity, univVars ++ variableList))
      case TFF.UnaryFormula(connective, body) => // change polarity
        connective match {
          case TFF.~ => TFF.UnaryFormula(connective, skolemizeTFFFormula0(name, body, !polarity, univVars))
        }
      case TFF.BinaryFormula(connective, left, right) => // change polarity for =>
        connective match {
          case TFF.<=> =>
            if (skolemizeAll || variableToSkolemize.isDefined)
              TFF.BinaryFormula(TFF.&,
                TFF.BinaryFormula(TFF.Impl, skolemizeTFFFormula0(name, left, !polarity, univVars), skolemizeTFFFormula0(name, right, polarity, univVars)),
                TFF.BinaryFormula(TFF.<=, skolemizeTFFFormula0(name, left, polarity, univVars),skolemizeTFFFormula0(name, right, !polarity, univVars))
              )
            else
              TFF.BinaryFormula(TFF.&,
                TFF.BinaryFormula(TFF.Impl, skolemizeTFFFormula0(name, left, !polarity, univVars), right),
                TFF.BinaryFormula(TFF.<=, skolemizeTFFFormula0(name, left, polarity, univVars), right)
              )
          case TFF.<~> =>
            if (skolemizeAll || variableToSkolemize.isDefined)
              TFF.BinaryFormula(TFF.~&,
                TFF.BinaryFormula(TFF.Impl, skolemizeTFFFormula0(name, left, polarity, univVars), skolemizeTFFFormula0(name, right, !polarity, univVars)),
                TFF.BinaryFormula(TFF.<=, skolemizeTFFFormula0(name, left, !polarity, univVars),skolemizeTFFFormula0(name, right, polarity, univVars))
              )
            else
              TFF.BinaryFormula(TFF.~&,
                TFF.BinaryFormula(TFF.Impl, skolemizeTFFFormula0(name, left, polarity, univVars), right),
                TFF.BinaryFormula(TFF.<=, skolemizeTFFFormula0(name, left, !polarity, univVars), right)
              )
          case TFF.Impl =>
            if (skolemizeAll || variableToSkolemize.isDefined) TFF.BinaryFormula(connective, skolemizeTFFFormula0(name, left, !polarity, univVars), skolemizeTFFFormula0(name, right, polarity, univVars))
            else TFF.BinaryFormula(connective, skolemizeTFFFormula0(name, left, !polarity, univVars), right)
          case TFF.<= =>
            if (skolemizeAll || variableToSkolemize.isDefined) TFF.BinaryFormula(connective, skolemizeTFFFormula0(name, left, polarity, univVars), skolemizeTFFFormula0(name, right, !polarity, univVars))
            else TFF.BinaryFormula(connective, skolemizeTFFFormula0(name, left, polarity, univVars), right)
          case TFF.~| | TFF.~& =>
            if (skolemizeAll || variableToSkolemize.isDefined) TFF.BinaryFormula(connective, skolemizeTFFFormula0(name, left, !polarity, univVars), skolemizeTFFFormula0(name, right, !polarity, univVars))
            else TFF.BinaryFormula(connective, skolemizeTFFFormula0(name, left, !polarity, univVars), right)
          case TFF.| | TFF.& =>
            if (skolemizeAll || variableToSkolemize.isDefined) TFF.BinaryFormula(connective, skolemizeTFFFormula0(name, left, polarity, univVars), skolemizeTFFFormula0(name, right, polarity, univVars))
            else TFF.BinaryFormula(connective, skolemizeTFFFormula0(name, left, polarity, univVars), right)
        }
      case TFF.ConditionalFormula(condition, thn, els) =>
        TFF.ConditionalFormula(skolemizeTFFFormula0(name, condition, !polarity, univVars), thn, els)
      case TFF.NonclassicalPolyaryFormula(connective, args) =>
        TFF.NonclassicalPolyaryFormula(connective, args.map(x => skolemizeTFFFormula0(name, x, polarity, univVars)))

      /*case TFF.LetFormula(typing, binding, body) => ???
      case TFF.FormulaVariable(name) => ???
      case TFF.Assignment(lhs, rhs) => ???
      case TFF.MetaIdentity(lhs, rhs) => ??? */

      case _ => formula
    }
  }

  private def skolemizeTFFFormula1(name: String, quantifier: TFF.Quantifier, variableList: Seq[TFF.TypedVariable],
                                   body: TFF.Formula, polarity: Boolean, univVars: Seq[TFF.TypedVariable]): TFF.Formula = {
    // if name check name (and recurse if no, and yes if yes), if no name do it and then return, otherwise
    variableToSkolemize match {
      case Some(variableName) =>
        // just skolemize that one
        if (variableList.exists(_._1 == variableName)) {
          variableExists = true
          val idxOfVariable = variableList.indexWhere(_._1 == variableName)
          val (before, after0) = variableList.splitAt(idxOfVariable)
          val theVariable = after0.head
          val after = after0.tail
          val skolemized = skolemizeTFFFormula2(name, body, theVariable, univVars)
          val rest = before ++ after
          if (rest.nonEmpty)  TFF.QuantifiedFormula(quantifier, before ++ after, skolemized)
          else skolemized
        } else /* recurse */ TFF.QuantifiedFormula(quantifier, variableList, skolemizeTFFFormula0(name, body, polarity, univVars))
      case None =>
        if (skolemizeAll) {
          val skolemized = variableList.foldLeft(body) { case (acc, variable) => skolemizeTFFFormula2(name, acc, variable, univVars) }
          skolemizeTFFFormula0(name, skolemized, polarity, univVars)
        } else {
          // only first occurrence and then return
          val theVariable = variableList.head
          val after = variableList.tail
          val skolemized = skolemizeTFFFormula2(name, body, theVariable, univVars)
          if (after.nonEmpty) TFF.QuantifiedFormula(quantifier, after, skolemized)
          else skolemized
        }
    }
  }
  private def skolemizeTFFFormula2(name: String, formula: TFF.Formula, variableToSkolemize: TFF.TypedVariable, universalVars: Seq[TFF.TypedVariable]): TFF.Formula = {
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
    val typeOfSkolemSymbol: TFF.Type =
      if (typesOfDependencies.isEmpty) goalTypeOfSkolemSymbol else TFF.MappingType(typesOfDependencies, goalTypeOfSkolemSymbol)
    val typeDeclaration: TPTP.TFFAnnotated = TPTP.TFFAnnotated(
      s"${skolemSymbol}_decl",
      "type",
      TFF.Typing(skolemSymbol, typeOfSkolemSymbol),
      None)
    typeDeclarationsOfIntroducedSkolemSymbols = typeDeclarationsOfIntroducedSkolemSymbols :+ typeDeclaration
    val skolemTerm: TFF.Term = TFF.AtomicTerm(skolemSymbol, universalVars.map { case (name, _) => TFF.Variable(name) })

    introducedSkolemSymbols = introducedSkolemSymbols + (variableToSkolemize._1 -> skolemSymbol)
    introducedSkolemTerms = introducedSkolemTerms + (variableToSkolemize._1 -> skolemTerm.pretty)
    if (choiceTerms) epsilonTermAxioms = epsilonTermAxioms :+ generateEpsilonTermTFF(name, skolemSymbol, skolemTerm,variableToSkolemize, universalVars, formula)

    replaceEveryVarOccurrenceWithTermTFF(formula, variableToSkolemize, skolemTerm)
  }

  private def generateEpsilonTermTFF(name: String, skolemSymbol: String, skolemTerm: TFF.Term, variableToSkolemize: TFF.TypedVariable, universalVars: Seq[TFF.TypedVariable], body: TFF.Formula): TPTP.AnnotatedFormula = {
    val epsilonFormula0: TFF.Formula = TFF.Equality(skolemTerm, TFF.FormulaTerm(TFF.QuantifiedFormula(TFF.Epsilon, Seq(variableToSkolemize), body)))
    val epsilonFormula: TFF.Formula =
      if (universalVars.isEmpty)
        epsilonFormula0
      else
        TFF.QuantifiedFormula(TFF.!, universalVars, epsilonFormula0)
    val annotations: TPTP.Annotations = generateEpsilonAnnotation(skolemSymbol, name)
    TPTP.TFFAnnotated(leo.datastructures.TPTP.escapeAtomicWord(s"${skolemSymbol}_defn"), "definition", TFF.Logical(epsilonFormula), annotations)
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
  private def skolemizeTHF(name: String, statement: TPTP.THF.Statement): TPTP.THF.Statement = {
    statement match {
      case THF.Logical(formula) => THF.Logical(skolemizeTHFFormula(name, formula))
      case _ => statement
    }
  }
  private def skolemizeTHFFormula(name: String, formula: TPTP.THF.Formula): TPTP.THF.Formula =
    skolemizeTHFFormula0(name, formula, polarity = true, univVars = Seq.empty)

  private def skolemizeTHFFormula0(name: String, formula: TPTP.THF.Formula, polarity: Boolean, univVars: Seq[THF.TypedVariable]): TPTP.THF.Formula = {
    formula match {
      // Act cases
      case THF.QuantifiedFormula(quantifier, variableList, body) if quantifier == TPTP.THF.? && polarity =>
        skolemizeTHFFormula1(name, quantifier, variableList, body, polarity, univVars)
      case THF.QuantifiedFormula(quantifier, variableList, body) if quantifier == TPTP.THF.! && !polarity =>
        skolemizeTHFFormula1(name, quantifier, variableList, body, polarity, univVars)
      // recursive cases with polarity switch
      /* the remaining quantifier cases are ! with positive polarity and ? with negative polarity, both are Skolem dependency variable cases for the recursion */
      case THF.QuantifiedFormula(quantifier, variableList, body) =>
        THF.QuantifiedFormula(quantifier, variableList, skolemizeTHFFormula0(name, body, polarity, univVars ++ variableList))
      case THF.FunctionTerm(f, args) =>
        THF.FunctionTerm(f, args) // TODO
      case THF.UnaryFormula(connective, body) => connective match {
        case THF.~ => THF.UnaryFormula(connective, skolemizeTHFFormula0(name, body, !polarity, univVars))
      }
      case THF.BinaryFormula(connective, left, right) =>
        connective match {
          case THF.<=> =>
            if (skolemizeAll || variableToSkolemize.isDefined)
              THF.BinaryFormula(THF.&,
                THF.BinaryFormula(THF.Impl, skolemizeTHFFormula0(name, left, !polarity, univVars), skolemizeTHFFormula0(name, right, polarity, univVars)),
                THF.BinaryFormula(THF.<=, skolemizeTHFFormula0(name, left, polarity, univVars), skolemizeTHFFormula0(name, right, !polarity, univVars)),
              )
            else
              THF.BinaryFormula(THF.&,
                THF.BinaryFormula(THF.Impl, skolemizeTHFFormula0(name, left, !polarity, univVars), right),
                THF.BinaryFormula(THF.<=, skolemizeTHFFormula0(name, left, polarity, univVars), right),
              )
          case THF.<~> =>
            if (skolemizeAll || variableToSkolemize.isDefined)
              THF.BinaryFormula(THF.~&,
                THF.BinaryFormula(THF.Impl, skolemizeTHFFormula0(name, left, polarity, univVars), skolemizeTHFFormula0(name, right, !polarity, univVars)),
                THF.BinaryFormula(THF.<=, skolemizeTHFFormula0(name, left, !polarity, univVars),skolemizeTHFFormula0(name, right, polarity, univVars))
              )
            else
              THF.BinaryFormula(THF.~&,
                THF.BinaryFormula(THF.Impl, skolemizeTHFFormula0(name, left, polarity, univVars), right),
                THF.BinaryFormula(THF.<=, skolemizeTHFFormula0(name, left, !polarity, univVars), right)
              )
          case THF.Impl =>
            if (skolemizeAll || variableToSkolemize.isDefined) THF.BinaryFormula(THF.Impl, skolemizeTHFFormula0(name, left, !polarity, univVars), skolemizeTHFFormula0(name, right, polarity, univVars))
            else THF.BinaryFormula(THF.Impl, skolemizeTHFFormula0(name, left, !polarity, univVars), right)
          case THF.<= =>
            if (skolemizeAll || variableToSkolemize.isDefined) THF.BinaryFormula(THF.<=, skolemizeTHFFormula0(name, left, polarity, univVars), skolemizeTHFFormula0(name, right, !polarity, univVars))
            else THF.BinaryFormula(THF.<=, skolemizeTHFFormula0(name, left, polarity, univVars), right)
          case THF.~| |  THF.~& =>
            if (skolemizeAll || variableToSkolemize.isDefined) THF.BinaryFormula(connective, skolemizeTHFFormula0(name, left, !polarity, univVars), skolemizeTHFFormula0(name, right, !polarity, univVars))
            else THF.BinaryFormula(connective, skolemizeTHFFormula0(name, left, !polarity, univVars), right)
          case THF.| | THF.& =>
            if (skolemizeAll || variableToSkolemize.isDefined) THF.BinaryFormula(connective, skolemizeTHFFormula0(name, left, polarity, univVars), skolemizeTHFFormula0(name, right, polarity, univVars))
            else THF.BinaryFormula(connective, skolemizeTHFFormula0(name, left, polarity, univVars), right)
          /*
          case THF.Eq => ???
          case THF.Neq => ???
          case THF.:= => ???
          case leo.datastructures.TPTP.THF.== => ???
          case THF.App => ???
          case THF.FunTyConstructor => ???
          case THF.ProductTyConstructor => ???
          case THF.SumTyConstructor => ???
           */
          case _ => formula
        }
      case THF.ConditionalTerm(_, _, _) => formula // TODO
      case THF.LetTerm(_, _, _) => formula // TODO
      case THF.NonclassicalPolyaryFormula(connective, args) =>
        THF.NonclassicalPolyaryFormula(connective, args.map(skolemizeTHFFormula0(name, _, polarity, univVars)))

      /*
      case THF.Variable(name) => ???
      case THF.DefinedTH1ConstantTerm(constant) => ???
      case THF.ConnectiveTerm(conn) => ???
      case THF.DistinctObject(name) => ???
      case THF.NumberTerm(value) => ???
      case THF.Tuple(elements) => ???
      */
      case _ => formula
    }
  }

  private def skolemizeTHFFormula1(name: String, quantifier: THF.Quantifier, variableList: Seq[THF.TypedVariable],
                                   body: THF.Formula, polarity: Boolean, univVars: Seq[THF.TypedVariable]): THF.Formula = {
    // if name check name (and recurse if no, and yes if yes), if no name do it and then return, otherwise
    variableToSkolemize match {
      case Some(variableName) =>
        // just skolemize that one
        if (variableList.exists(_._1 == variableName)) {
          variableExists = true
          val idxOfVariable = variableList.indexWhere(_._1 == variableName)
          val (before, after0) = variableList.splitAt(idxOfVariable)
          val theVariable = after0.head
          val after = after0.tail
          val skolemized = skolemizeTHFFormula2(name, body, theVariable, univVars)
          val rest = before ++ after
          if (rest.nonEmpty)  THF.QuantifiedFormula(quantifier, before ++ after, skolemized)
          else skolemized
        } else /* recurse */ THF.QuantifiedFormula(quantifier, variableList, skolemizeTHFFormula0(name, body, polarity, univVars))
      case None =>
        if (skolemizeAll) {
          val skolemized = variableList.foldLeft(body) { case (acc, variable) => skolemizeTHFFormula2(name, acc, variable, univVars) }
          skolemizeTHFFormula0(name, skolemized, polarity, univVars)
        } else {
          // only first occurrence and then return
          val theVariable = variableList.head
          val after = variableList.tail
          val skolemized = skolemizeTHFFormula2(name, body, theVariable, univVars)
          if (after.nonEmpty) THF.QuantifiedFormula(quantifier, after, skolemized)
          else skolemized
        }
    }
  }
  private def skolemizeTHFFormula2(name: String, formula: THF.Formula, variableToSkolemize: THF.TypedVariable, universalVars: Seq[THF.TypedVariable]): THF.Formula = {
    val skolemSymbol: String = freshSkolemSymbol()
    val goalTypeOfSkolemSymbol = variableToSkolemize._2
    val typesOfDependencies = universalVars.map(_._2)
    val typeOfSkolemSymbol: THF.Type = typesOfDependencies.foldRight(goalTypeOfSkolemSymbol){ case (ty, acc) =>
      THF.BinaryFormula(THF.FunTyConstructor, ty, acc)
    }
    val typeDeclaration: TPTP.THFAnnotated = TPTP.THFAnnotated(
      s"${skolemSymbol}_decl",
      "type",
      THF.Typing(skolemSymbol, typeOfSkolemSymbol),
      None)
    typeDeclarationsOfIntroducedSkolemSymbols = typeDeclarationsOfIntroducedSkolemSymbols :+ typeDeclaration

    val skolemTerm: THF.Formula = THF.FunctionTerm(skolemSymbol, universalVars.map { case (name, _) => THF.Variable(name) })

    introducedSkolemSymbols = introducedSkolemSymbols + (variableToSkolemize._1 -> skolemSymbol)
    introducedSkolemTerms = introducedSkolemTerms + (variableToSkolemize._1 -> skolemTerm.pretty)
    if (choiceTerms) epsilonTermAxioms = epsilonTermAxioms :+ generateEpsilonTermTHF(name, skolemSymbol, skolemTerm,variableToSkolemize, universalVars, formula)
    replaceEveryVarOccurrenceWithTermTHF(formula, variableToSkolemize, skolemTerm)
  }


  private def generateEpsilonTermTHF(name: String, skolemSymbol: String, skolemTerm: THF.Formula, variableToSkolemize: THF.TypedVariable, universalVars: Seq[THF.TypedVariable], body: THF.Formula): TPTP.AnnotatedFormula = {
    val epsilonFormula0: THF.Formula = THF.BinaryFormula(THF.Eq, skolemTerm, THF.QuantifiedFormula(THF.Epsilon, Seq(variableToSkolemize), body))
    val epsilonFormula: THF.Formula =
      if (universalVars.isEmpty)
        epsilonFormula0
      else
        THF.QuantifiedFormula(THF.!, universalVars, epsilonFormula0)
    val annotations: TPTP.Annotations = generateEpsilonAnnotation(skolemSymbol, name)
    TPTP.THFAnnotated(leo.datastructures.TPTP.escapeAtomicWord(s"${skolemSymbol}_defn"), "definition", THF.Logical(epsilonFormula), annotations)
  }
  private def replaceEveryVarOccurrenceWithTermTHF(formula: TPTP.THF.Formula, variable: THF.TypedVariable, term: TPTP.THF.Formula): THF.Formula = {
    formula match {
      case THF.FunctionTerm(f, args) => THF.FunctionTerm(f, args.map(replaceEveryVarOccurrenceWithTermTHF(_, variable, term)))
      case THF.QuantifiedFormula(quantifier, variableList, body) =>
        THF.QuantifiedFormula(quantifier, variableList, replaceEveryVarOccurrenceWithTermTHF(body, variable, term))
      case THF.Variable(name) =>
        if (name == variable._1) term
        else formula
      case THF.UnaryFormula(connective, body) =>
        THF.UnaryFormula(connective, replaceEveryVarOccurrenceWithTermTHF(body, variable, term))
      case THF.BinaryFormula(connective, left, right) =>
        THF.BinaryFormula(connective,
          replaceEveryVarOccurrenceWithTermTHF(left, variable, term),
          replaceEveryVarOccurrenceWithTermTHF(right, variable, term))
      case THF.Tuple(elements) => THF.Tuple(elements.map(replaceEveryVarOccurrenceWithTermTHF(_,variable, term)))
      case THF.NonclassicalPolyaryFormula(connective, args) =>
        THF.NonclassicalPolyaryFormula(connective, args.map(replaceEveryVarOccurrenceWithTermTHF(_, variable, term)))
      case THF.ConditionalTerm(_, _, _) => formula // TODO
      case THF.LetTerm(typing, binding, body) => // TODO
        THF.LetTerm(typing,
          binding.map { case (l, r) => (l, replaceEveryVarOccurrenceWithTermTHF(r, variable, term))},
          replaceEveryVarOccurrenceWithTermTHF(body, variable, term))
      /*case THF.DefinedTH1ConstantTerm(constant) => ???
      case THF.ConnectiveTerm(conn) => ???
      case THF.DistinctObject(name) => ???
      case THF.NumberTerm(value) => ???*/
      case _ => formula
    }
  }


  /* introduced(definition,[new_symbols(skolem,[<skolem symbol>])],[<parent>]) */
  private[this] def generateEpsilonAnnotation(introducedSymbol: String, parent: String): TPTP.Annotations = {
    // Oh boy ...
    def inferenceTerm: TPTP.GeneralTerm =
      TPTP.GeneralTerm(
        Seq(
          TPTP.MetaFunctionData("introduced",
            Seq(
              // Entry #1 "definition"
              TPTP.GeneralTerm(
                Seq(TPTP.MetaFunctionData("definition", Seq.empty)),
                None
              ),
              // Entry #2 [new_symbols(skolem, [<introduced symbol>])]
              TPTP.GeneralTerm(
                Seq.empty,
                Some( // Tuple begin
                  Seq(
                    TPTP.GeneralTerm(
                      Seq(
                        TPTP.MetaFunctionData("new_symbols", Seq(
                          TPTP.GeneralTerm(Seq(TPTP.MetaFunctionData("skolem", Seq.empty)),None),
                          TPTP.GeneralTerm(Seq.empty,Some(Seq(TPTP.GeneralTerm(Seq(TPTP.MetaFunctionData(introducedSymbol, Seq.empty)), None))))
                        ))
                      ),
                      None
                    )
                  )
                ) // Tuple end
              ),
              // Entry #3: [<parent>]
              TPTP.GeneralTerm(
                Seq.empty,
                Some(
                  Seq(
                    TPTP.GeneralTerm(
                      Seq(TPTP.MetaFunctionData(parent, Seq.empty)),
                      None
                    )
                  )
                )
              )
            )
          )
        ), None)
    Some((inferenceTerm, None))
  }

  /* if no choice terms:
       introduced(assumption,[new_symbols(skolem,[<skolem symbol>]),bind(<variable>,<skolem term>)],[<parent>])
     if choice terms:
       introduced(assumption,[bind(<variable>,<skolem term>)],[<parent>])
   */
  @inline private[this] def assumptionAnnotation(formula: TPTP.AnnotatedFormula): TPTP.Annotations = Some((inferenceTerm(formula), None))
  @inline private[this] def inferenceTerm(formula: TPTP.AnnotatedFormula): TPTP.GeneralTerm = {
    TPTP.GeneralTerm(
      Seq(
        TPTP.MetaFunctionData("introduced",
          Seq(
            // Entry #1 assumption
            assumptionsTerm,
            // Entry #2 [new_symbols(skolem,[<skolem symbol>]),bind(<variable>,<skolem term>)] possibly without the new_symbols
            newSymbolsAndBind(withNewSymbolsAnnotation = !choiceTerms),
            // Entry #3: [<parent>]
            parentTerm(formula)
          )
        )
      ), None)
  }
  @inline private[this] def assumptionsTerm: TPTP.GeneralTerm = TPTP.GeneralTerm(
    Seq(TPTP.MetaFunctionData("assumption", Seq.empty)),
    None
  )
  @inline private[this] def newSymbolsAndBind(withNewSymbolsAnnotation: Boolean): TPTP.GeneralTerm = TPTP.GeneralTerm(
    Seq.empty,
    Some( // Tuple begin
      if (withNewSymbolsAnnotation) {
        Seq(
          // Entry 2.1: new_symbols
          TPTP.GeneralTerm(
            Seq(
              TPTP.MetaFunctionData("new_symbols", Seq(
                TPTP.GeneralTerm(Seq(TPTP.MetaFunctionData("skolem", Seq.empty)),None),
                TPTP.GeneralTerm(Seq.empty,Some(
                  introducedSkolemSymbols.values.toSeq.map(sym => TPTP.GeneralTerm(Seq(TPTP.MetaFunctionData(sym, Seq.empty)), None))
                ))
              ))
            ),
            None
          ))
      } else {
        Seq.empty
      }
       ++
        // Entry 2.2: bind(...)
          introducedSkolemTerms.map { case (vari,term) =>
            TPTP.GeneralTerm(Seq(TPTP.MetaFunctionData("bind", Seq(
              TPTP.GeneralTerm(Seq(TPTP.MetaFunctionData(vari, Seq.empty)),None),
              TPTP.GeneralTerm(Seq(TPTP.MetaFunctionData(term, Seq.empty)),None)
            ))), None)
          }.toSeq
    ) // Tuple end
  )
  @inline private[this] def parentTerm(formula: TPTP.AnnotatedFormula): TPTP.GeneralTerm = TPTP.GeneralTerm(
    Seq.empty,
    Some(
      Seq(
        TPTP.GeneralTerm(
          Seq(TPTP.MetaFunctionData(formula.name, Seq.empty)),
          None
        )
      )
    )
  )
}
