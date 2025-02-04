package lisa.proven

import lisa.automation.kernel.SimplePropositionalSolver as SPS
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheory.PredicateLogic
import lisa.kernel.proof.SCProofChecker
import lisa.tptp.KernelParser.*
import lisa.tptp.ProblemGatherer.getPRPproblems
import lisa.utils.FOLPrinter
import lisa.utils.Helpers.*
import org.scalatest.funsuite.AnyFunSuite

import scala.language.adhocExtensions

class SimpleProverTests extends AnyFunSuite {

  /*
    test("Simple propositional logic proofs") {
        val problems = getPRPproblems.take(1)
        problems.foreach( pr => {
            println("--- Problem "+pr.file)
            val sq = problemToSequent(pr)
            println(FOLPrinter.prettySequent(sq))
            val proof = SPS.solveSequent(sq)
            if (!Seq("Unsatisfiable", "Theorem", "Satisfiable").contains(pr.status)) println("Unknown status: "+pr.status+", "+pr.file)

            assert(SCProofChecker.checkSCProof(proof).isValid == (pr.status =="Unsatisfiable" || pr.status == "Theorem"))

        })

    }
   */
}
