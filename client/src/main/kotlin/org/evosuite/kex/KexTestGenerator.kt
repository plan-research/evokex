package org.evosuite.kex

import kotlinx.collections.immutable.PersistentList
import kotlinx.collections.immutable.PersistentMap
import kotlinx.collections.immutable.toPersistentList
import kotlinx.collections.immutable.toPersistentMap
import kotlinx.coroutines.DelicateCoroutinesApi
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.withTimeoutOrNull
import kotlinx.serialization.Contextual
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.InternalSerializationApi
import org.evosuite.Properties
import org.evosuite.kex.observers.KexTestObserver
import org.evosuite.testcase.DefaultTestCase
import org.evosuite.testcase.TestCase
import org.evosuite.testcase.TestChromosome
import org.evosuite.testcase.statements.PrimitiveStatement
import org.slf4j.LoggerFactory
import org.vorpal.research.kex.asm.analysis.concolic.bfs.BfsPathSelectorImpl
import org.vorpal.research.kex.asm.analysis.concolic.coverage.CoverageGuidedSelector
import org.vorpal.research.kex.asm.analysis.concolic.coverage.CoverageGuidedSelectorManager
import org.vorpal.research.kex.asm.state.PredicateStateAnalysis
import org.vorpal.research.kex.config.kexConfig
import org.vorpal.research.kex.descriptor.Descriptor
import org.vorpal.research.kex.ktype.KexType
import org.vorpal.research.kex.mocking.performMocking
import org.vorpal.research.kex.parameters.Parameters
import org.vorpal.research.kex.parameters.concreteParameters
import org.vorpal.research.kex.parameters.filterIgnoredStatic
import org.vorpal.research.kex.parameters.filterStaticFinals
import org.vorpal.research.kex.reanimator.actionsequence.ActionSequence
import org.vorpal.research.kex.reanimator.actionsequence.generator.ConcolicSequenceGenerator
import org.vorpal.research.kex.reanimator.rtUnmapped
import org.vorpal.research.kex.smt.AsyncChecker
import org.vorpal.research.kex.smt.Checker
import org.vorpal.research.kex.smt.SMTModel
import org.vorpal.research.kex.state.PredicateState
import org.vorpal.research.kex.state.term.*
import org.vorpal.research.kex.state.transformer.generateInitialDescriptors
import org.vorpal.research.kex.trace.symbolic.*
import org.vorpal.research.kex.trace.symbolic.protocol.SuccessResult
import org.vorpal.research.kex.util.asmString
import org.vorpal.research.kfg.Package
import org.vorpal.research.kfg.ir.*
import org.vorpal.research.kfg.ir.value.instruction.Instruction
import org.vorpal.research.kthelper.assert.unreachable
import java.util.*
import kotlin.time.Duration.Companion.seconds
import kotlin.time.ExperimentalTime

@ExperimentalTime
@InternalSerializationApi
@ExperimentalSerializationApi
@DelicateCoroutinesApi
class KexTestGenerator {

    companion object {
        private val logger = LoggerFactory.getLogger(KexTestGenerator::class.java)
    }

    private val ctx get() = KexService.ctx
    private val pathSelector = CoverageGuidedSelector(
        CoverageGuidedSelectorManager(
            ctx, ctx.cm[Properties.TARGET_CLASS.asmString].allMethods
        )
    )
    private val asGenerator = ConcolicSequenceGenerator(ctx, PredicateStateAnalysis(ctx.cm))
    private val cache = WeakHashMap<TestChromosome, SymbolicState>()

    fun collectTraces(testChromosomes: List<TestChromosome>, stoppingCondition: () -> Boolean) {
        runBlocking {
            logger.info("Trace collection")
            for (test in testChromosomes) {
                if (stoppingCondition()) break
                if (test in cache) continue

                try {
                    val observer = KexTestObserver(ctx)
                    val testCaseClone = test.testCase.clone() as DefaultTestCase
                    KexService.execute(testCaseClone, observer)

                    cache[test] = observer.trace
                } catch (e: Throwable) {
                    logger.error("Error occurred while running test:\n{}", test, e)
                }
            }
        }
    }

    private suspend fun updateWithTrace(trace: List<Instruction>, state: SymbolicState, method: Method) {
        pathSelector.addExecutionTrace(method, persistentSymbolicState(), SuccessResult(trace, state))
    }

    fun generateTest(): TestCase? = runBlocking {
        logger.info("Generating test with kex")

        val mth = buildMethod()
        var chosenTest: TestChromosome
        var chosenPathClauseIndex: Pair<Int, Int>
        do {
            chosenTest = chooseTestCase()
            chosenPathClauseIndex = choosePathClause(chosenTest)
        } while(chosenPathClauseIndex.first == -1)

        val prevState = cache[chosenTest]!!
        val clauseList = prevState.clauses.take(chosenPathClauseIndex.first).toMutableList()
        val pathList = prevState.path.take(chosenPathClauseIndex.second).toMutableList()
        val reversed = BfsPathSelectorImpl(ctx, mth).reverse(pathList.last())!!
        clauseList[clauseList.size - 1] = reversed
        pathList[pathList.size - 1] = reversed

        val state = PersistentSymbolicState(
            PersistentClauseList(clauseList.toPersistentList()),
            PersistentPathCondition(pathList.toPersistentList()),
            prevState.concreteTypes.toPersistentMap(),
            prevState.concreteValues.toPersistentMap(),
            prevState.termMap.toPersistentMap()
        )

        val result = state.check(ctx) ?: return@runBlocking null
        return@runBlocking generateTest(chosenTest.testCase, result)
    }.also {
        logger.debug("Kex produce new test:\n{}", it)
    }

    private fun findNext(assignments: Map<Term, Term>, previous: String? = null): Term? {
        var flag = previous == null
        for ((key, _) in assignments) {
            if (!key.name.contains("primitive")) {
                continue
            }
            if (key.name == previous) {
                flag = true
                continue
            }
            if (flag) {
                return key
            }
        }
        return null
    }

    private fun generateTest(oldTest: TestCase, result: SMTModel): TestCase? {
        var isTestChanged = false
        val newTest = DefaultTestCase()
        var curPrimitiveName = findNext(result.assignments)
        for (s in oldTest) {
            if (curPrimitiveName == null) {
                return null
            }
            if (s is PrimitiveStatement<*>) {
                isTestChanged = true
                when (result.assignments[curPrimitiveName]) {
                    is ConstIntTerm -> {
                        s.value = (result.assignments[curPrimitiveName] as ConstIntTerm).value
                    }

                    is ConstLongTerm -> {
                        s.value = (result.assignments[curPrimitiveName] as ConstLongTerm).value
                    }

                    is ConstFloatTerm -> {
                        s.value = (result.assignments[curPrimitiveName] as ConstFloatTerm).value
                    }

                    is ConstDoubleTerm -> {
                        s.value = (result.assignments[curPrimitiveName] as ConstDoubleTerm).value
                    }

                    is ConstStringTerm -> {
                        s.value = (result.assignments[curPrimitiveName] as ConstStringTerm).value
                    }

                    is ConstShortTerm -> {
                        s.value = (result.assignments[curPrimitiveName] as ConstShortTerm).value
                    }

                    is ConstByteTerm -> {
                        s.value = (result.assignments[curPrimitiveName] as ConstByteTerm).value
                    }

                    is ConstCharTerm -> {
                        s.value = (result.assignments[curPrimitiveName] as ConstCharTerm).value
                    }

                    is ConstBoolTerm -> {
                        s.value = (result.assignments[curPrimitiveName] as ConstBoolTerm).value
                    }

                    else -> unreachable {}
                }
                curPrimitiveName = findNext(result.assignments, curPrimitiveName?.name)
            }
            newTest.addStatement(s)
        }

        if (isTestChanged)
            return newTest
        return null
    }

    private fun chooseTestCase(): TestChromosome {
        return cache.keys.random()
    }

    private fun choosePathClause(chosenTest: TestChromosome): Pair<Int, Int> {
        if (cache[chosenTest]!!.path.path.isEmpty())
            return -1 to -1
        val number = (0 until cache[chosenTest]!!.path.path.size).random()
        var counter = 0
        for (i in 0 until cache[chosenTest]!!.clauses.state.size) {
            if (cache[chosenTest]!!.clauses.state[i] is PathClause) {
                if (counter == number) {
                    return i + 1 to number + 1
                }
                counter += 1
            }
        }
        return -1 to -1
    }

    private fun buildMethod(): Method {
        val cm = KexService.ctx.cm
        val klass: Class = OuterClass(cm, Package(""), "TestClass", Modifiers(0))
        val testDescriptor = MethodDescriptor(emptyList(), cm.type.voidType)
        return Method(cm, klass, "name", testDescriptor)
    }
}