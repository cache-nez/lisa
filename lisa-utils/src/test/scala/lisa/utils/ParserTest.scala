package lisa.utils

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.utils.Helpers.*
import org.scalatest.funsuite.AnyFunSuite

class ParserTest extends AnyFunSuite with TestUtils {
  val parser = Parser()

  test("constant") {
    assert(parser.parseTerm("x") == FunctionTerm(cx, Seq()))
  }

  test("variable") {
    assert(parser.parseTerm("?x") == VariableTerm(x))
  }

  test("constant function application") {
    assert(parser.parseTerm("f()") == FunctionTerm(f0, Seq()))
    assert(parser.parseTerm("f(x)") == FunctionTerm(f1, Seq(cx)))
    assert(parser.parseTerm("f(x, y)") == FunctionTerm(f2, Seq(cx, cy)))
    assert(parser.parseTerm("f(x, y, z)") == FunctionTerm(f3, Seq(cx, cy, cz)))

    assert(parser.parseTerm("f(?x)") == FunctionTerm(f1, Seq(x)))
    assert(parser.parseTerm("f(?x, ?y)") == FunctionTerm(f2, Seq(x, y)))
    assert(parser.parseTerm("f(?x, ?y, ?z)") == FunctionTerm(f3, Seq(x, y, z)))
  }

  test("schematic function application") {
    // parser.parseTerm("?f()") -- schematic functions of 0 arguments do not exist, those are variables
    assert(parser.parseTerm("?f(x)") == FunctionTerm(sf1, Seq(cx)))
    assert(parser.parseTerm("?f(x, y)") == FunctionTerm(sf2, Seq(cx, cy)))
    assert(parser.parseTerm("?f(x, y, z)") == FunctionTerm(sf3, Seq(cx, cy, cz)))

    assert(parser.parseTerm("?f(?x)") == FunctionTerm(sf1, Seq(x)))
    assert(parser.parseTerm("?f(?x, ?y)") == FunctionTerm(sf2, Seq(x, y)))
    assert(parser.parseTerm("?f(?x, ?y, ?z)") == FunctionTerm(sf3, Seq(x, y, z)))
  }

  test("nested function application") {
    assert(parser.parseTerm("?f(?f(?x), ?y)") == FunctionTerm(sf2, Seq(FunctionTerm(sf1, Seq(x)), y)))
  }

  test("0-ary predicate") {
    assert(parser.parseFormula("a") == PredicateFormula(ConstantPredicateLabel("a", 0), Seq()))
    assert(parser.parseFormula("a()") == PredicateFormula(ConstantPredicateLabel("a", 0), Seq()))
  }

  test("boolean constants") {
    assert(parser.parseFormula("true") == True)
    assert(parser.parseFormula("True") == True)
    assert(parser.parseFormula("T") == True)
    assert(parser.parseFormula("⊤") == True)

    assert(parser.parseFormula("false") == False)
    assert(parser.parseFormula("False") == False)
    assert(parser.parseFormula("F") == False)
    assert(parser.parseFormula("⊥") == False)
  }

  test("predicate application") {
    assert(parser.parseFormula("p(x, y, z)") == PredicateFormula(ConstantPredicateLabel("p", 3), Seq(cx, cy, cz)))
    assert(parser.parseFormula("p(?x, ?y, ?z)") == PredicateFormula(ConstantPredicateLabel("p", 3), Seq(x, y, z)))
  }

  test("equality") {
    assert(parser.parseFormula("(x = x)") == PredicateFormula(equality, Seq(cx, cx)))
    assert(parser.parseFormula("x = x") == PredicateFormula(equality, Seq(cx, cx)))
    assert(parser.parseFormula("a ∧ (?x = ?x)") == ConnectorFormula(And, Seq(a, PredicateFormula(equality, Seq(x, x)))))
  }

  test("unicode connectors") {
    assert(parser.parseFormula("¬a") == ConnectorFormula(Neg, Seq(a)))
    assert(parser.parseFormula("a ∧ b") == ConnectorFormula(And, Seq(a, b)))
    assert(parser.parseFormula("a ∨ b") == ConnectorFormula(Or, Seq(a, b)))
    assert(parser.parseFormula("a ⇒ b") == ConnectorFormula(Implies, Seq(a, b)))
    assert(parser.parseFormula("a ↔ b") == ConnectorFormula(Iff, Seq(a, b)))
  }

  test("ascii connectors") {
    assert(parser.parseFormula("!a") == ConnectorFormula(Neg, Seq(a)))
    assert(parser.parseFormula("a /\\ b") == ConnectorFormula(And, Seq(a, b)))
    assert(parser.parseFormula("a \\/ b") == ConnectorFormula(Or, Seq(a, b)))
    assert(parser.parseFormula("a => b") == ConnectorFormula(Implies, Seq(a, b)))
    assert(parser.parseFormula("a ==> b") == ConnectorFormula(Implies, Seq(a, b)))
    assert(parser.parseFormula("a <=> b") == ConnectorFormula(Iff, Seq(a, b)))
  }

  test("connector associativity") {
    assert(parser.parseFormula("a ∧ b ∧ c") == ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(a, b)), c)))
    assert(parser.parseFormula("a ∨ b ∨ c") == ConnectorFormula(Or, Seq(ConnectorFormula(Or, Seq(a, b)), c)))
  }

  test("connector priority") {
    // a ∨ (b ∧ c)
    assert(parser.parseFormula("a ∨ b ∧ c") == ConnectorFormula(Or, Seq(a, ConnectorFormula(And, Seq(b, c)))))
    // (a ∧ b) ∨ c
    assert(parser.parseFormula("a ∧ b ∨ c") == ConnectorFormula(Or, Seq(ConnectorFormula(And, Seq(a, b)), c)))

    // (a ∧ b) => c
    assert(parser.parseFormula("a ∧ b => c") == ConnectorFormula(Implies, Seq(ConnectorFormula(And, Seq(a, b)), c)))
    // a => (b ∧ c)
    assert(parser.parseFormula("a => b ∧ c") == ConnectorFormula(Implies, Seq(a, ConnectorFormula(And, Seq(b, c)))))
    // (a ∨ b) => c
    assert(parser.parseFormula("a ∨ b => c") == ConnectorFormula(Implies, Seq(ConnectorFormula(Or, Seq(a, b)), c)))
    // a => (b ∨ c)
    assert(parser.parseFormula("a => b ∨ c") == ConnectorFormula(Implies, Seq(a, ConnectorFormula(Or, Seq(b, c)))))

    // (a ∧ b) <=> c
    assert(parser.parseFormula("a ∧ b <=> c") == ConnectorFormula(Iff, Seq(ConnectorFormula(And, Seq(a, b)), c)))
    // a <=> (b ∧ c)
    assert(parser.parseFormula("a <=> b ∧ c") == ConnectorFormula(Iff, Seq(a, ConnectorFormula(And, Seq(b, c)))))
    // (a ∨ b) <=> c
    assert(parser.parseFormula("a ∨ b <=> c") == ConnectorFormula(Iff, Seq(ConnectorFormula(Or, Seq(a, b)), c)))
    // a <=> (b ∨ c)
    assert(parser.parseFormula("a <=> b ∨ c") == ConnectorFormula(Iff, Seq(a, ConnectorFormula(Or, Seq(b, c)))))
  }

  test("connector parentheses") {
    assert(parser.parseFormula("(a ∨ b) ∧ c") == ConnectorFormula(And, Seq(ConnectorFormula(Or, Seq(a, b)), c)))
    assert(parser.parseFormula("a ∧ (b ∨ c)") == ConnectorFormula(And, Seq(a, ConnectorFormula(Or, Seq(b, c)))))
  }

  test("quantifiers") {
    assert(parser.parseFormula("∀ ?x. (p)") == BinderFormula(Forall, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))
    assert(parser.parseFormula("∃ ?x. (p)") == BinderFormula(Exists, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))
    assert(parser.parseFormula("∃! ?x. (p)") == BinderFormula(ExistsOne, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))

    assert(parser.parseFormula("∀ ?x. p") == BinderFormula(Forall, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))
    assert(parser.parseFormula("∃ ?x. p") == BinderFormula(Exists, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))
    assert(parser.parseFormula("∃! ?x. p") == BinderFormula(ExistsOne, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))
  }

  test("nested quantifiers") {
    assert(parser.parseFormula("∀x. ∃y. ∃!z. a") == BinderFormula(Forall, x, BinderFormula(Exists, y, BinderFormula(ExistsOne, z, a))))
  }

  test("quantifier parentheses") {
    assert(parser.parseFormula("∀x. b ∧ a") == BinderFormula(Forall, x, ConnectorFormula(And, Seq(b, a))))
    assert(
      parser.parseFormula("∀ ?x. p(?x) ∧ q(?x)") == BinderFormula(
        Forall,
        x,
        ConnectorFormula(And, Seq(PredicateFormula(ConstantPredicateLabel("p", 1), Seq(x)), PredicateFormula(ConstantPredicateLabel("q", 1), Seq(x))))
      )
    )

    assert(parser.parseFormula("(∀x. b) ∧ a") == ConnectorFormula(And, Seq(BinderFormula(Forall, x, b), a)))

    assert(
      parser.parseFormula("(∀ ?x. p(?x)) ∧ q(?x)") == ConnectorFormula(
        And,
        Seq(
          BinderFormula(Forall, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 1), Seq(x))),
          PredicateFormula(ConstantPredicateLabel("q", 1), Seq(x))
        )
      )
    )

    assert(parser.parseFormula("a ∧ (∀x. b) ∨ a") == ConnectorFormula(Or, Seq(ConnectorFormula(And, Seq(a, BinderFormula(Forall, x, b))), a)))
    assert(parser.parseFormula("(a ∧ (∀x. b)) ∧ a") == ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(a, BinderFormula(Forall, x, b))), a)))
  }

  test("complex formulas with connectors") {
    assert(parser.parseFormula("¬(a ∨ b)") == ConnectorFormula(Neg, Seq(ConnectorFormula(Or, Seq(a, b)))))
    assert(parser.parseFormula("¬(¬a)") == ConnectorFormula(Neg, Seq(ConnectorFormula(Neg, Seq(a)))))
    assert(parser.parseFormula("¬¬a") == ConnectorFormula(Neg, Seq(ConnectorFormula(Neg, Seq(a)))))
    assert(parser.parseFormula("¬¬(a ∧ b)") == ConnectorFormula(Neg, Seq(ConnectorFormula(Neg, Seq(ConnectorFormula(And, Seq(a, b)))))))
    assert(parser.parseFormula("¬a ∧ ¬b ∧ ¬c") == ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(ConnectorFormula(Neg, Seq(a)), ConnectorFormula(Neg, Seq(b)))), ConnectorFormula(Neg, Seq(c)))))
  }

  test("complex formulas") {
    assert(parser.parseFormula("∀x. ?x = ?x") == BinderFormula(Forall, x, PredicateFormula(equality, Seq(x, x))))
  }

  test("parser limitations") {
    // TODO: more specific error reporting check
    assertThrows[ParserException](parser.parseFormula("(a ∧ ∀x. b) ∧ a"))

  }

  test("sequent") {
    val forallEq = BinderFormula(Forall, x, PredicateFormula(equality, Seq(x, x)))
    assert(parser.parseSequent("∀x. ?x = ?x") == Sequent(Set(), Set(forallEq)))
    assert(parser.parseSequent("⊢ ∀x. ?x = ?x") == Sequent(Set(), Set(forallEq)))
    assert(parser.parseSequent("∀x. ?x = ?x ⊢ ∀x. ?x = ?x") == Sequent(Set(forallEq), Set(forallEq)))
    val existsXEq = BinderFormula(Exists, x, PredicateFormula(equality, Seq(x, x)))
    assert(parser.parseSequent("∀x. ?x = ?x ⊢ ∃x. ?x = ?x") == Sequent(Set(forallEq), Set(existsXEq)))
    val existsYEq = BinderFormula(Exists, y, PredicateFormula(equality, Seq(y, y)))
    assert(parser.parseSequent("∀x. ?x = ?x ⊢ ∃x. ?x = ?x; ∃y. ?y = ?y") == Sequent(Set(forallEq), Set(existsYEq, existsXEq)))
    assert(
      parser.parseSequent("p ; ∀x. ?x = ?x ⊢ ∃x. ?x = ?x; ∃y. ?y = ?y") ==
        Sequent(Set(forallEq, PredicateFormula(ConstantPredicateLabel("p", 0), Seq())), Set(existsYEq, existsXEq))
    )
  }

  test("sequents from Mapping and SetTheory") {
    val va = VariableLabel("a")
    val leftAndRight = BinderFormula(ExistsOne, x, PredicateFormula(sPhi2, Seq(x, va)))
    assert(parser.parseSequent("∃!x. ?phi(?x, ?a) ⊢ ∃!x. ?phi(?x, ?a)") == Sequent(Set(leftAndRight), Set(leftAndRight)))

    assert(
      parser.parseSequent("∀x. (?x = ?x1) ↔ ?phi(?x) ⊢ (?z = ?f(?x1)) ⇒ (∃x. (?z = ?f(?x)) ∧ ?phi(?x))") == Sequent(
        Set(BinderFormula(Forall, x, ConnectorFormula(Iff, Seq(x === x1, sPhi1(x))))),
        Set((z === sf1(x1)) ==> exists(x, (z === sf1(x)) /\ sPhi1(x)))
      )
    )
    assert(
      parser.parseSequent("∃x1. ∀x. (?x = ?x1) ↔ ?phi(?x) ⊢ ∃z1. ∀z. (?z = ?z1) ↔ (∃x. (?z = ?f(?x)) ∧ ?phi(?x))") == (exists(x1, forall(x, (x === x1) <=> (sPhi1(x)))) |- exists(
        z1,
        forall(z, (z === z1) <=> exists(x, (z === sf1(x)) /\ sPhi1(x)))
      ))
    )
    assert(parser.parseSequent("⊢ (?x = ?x) ∨ (?x = ?y)") == (() |- (x === x) \/ (x === y)))
    assert(
      parser.parseSequent("(?x = ?x) ∨ (?x = ?y); (?x = ?x) ∨ (?x = ?y) ↔ (?x = ?x') ∨ (?x = ?y') ⊢ (?x = ?x') ∨ (?x = ?y')") == (Set(
        (x === x) \/ (x === y),
        ((x === x) \/ (x === y)) <=> ((x === xPrime) \/ (x === yPrime))
      ) |- (x === xPrime) \/ (x === yPrime))
    )
  }
}
