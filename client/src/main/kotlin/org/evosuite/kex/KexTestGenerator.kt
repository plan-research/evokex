package org.evosuite.kex

import kotlinx.collections.immutable.toPersistentList
import kotlinx.collections.immutable.toPersistentMap
import kotlinx.coroutines.DelicateCoroutinesApi
import kotlinx.coroutines.runBlocking
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.InternalSerializationApi
import org.evosuite.Properties
import org.evosuite.kex.observers.KexTestObserver
import org.evosuite.testcase.DefaultTestCase
import org.evosuite.testcase.TestCase
import org.evosuite.testcase.TestChromosome
import org.evosuite.testcase.statements.PrimitiveStatement
import org.evosuite.testcase.statements.StringPrimitiveStatement
import org.evosuite.testcase.statements.numeric.BooleanPrimitiveStatement
import org.evosuite.testcase.statements.numeric.BytePrimitiveStatement
import org.evosuite.testcase.statements.numeric.CharPrimitiveStatement
import org.evosuite.testcase.statements.numeric.DoublePrimitiveStatement
import org.evosuite.testcase.statements.numeric.FloatPrimitiveStatement
import org.evosuite.testcase.statements.numeric.IntPrimitiveStatement
import org.evosuite.testcase.statements.numeric.LongPrimitiveStatement
import org.evosuite.testcase.statements.numeric.ShortPrimitiveStatement
import org.slf4j.LoggerFactory
import org.vorpal.research.kex.asm.analysis.concolic.bfs.BfsPathSelectorImpl
import org.vorpal.research.kex.descriptor.*
import org.vorpal.research.kex.ktype.KexChar
import org.vorpal.research.kex.ktype.asArray
import org.vorpal.research.kex.smt.InitialDescriptorReanimator
import org.vorpal.research.kex.smt.SMTModel
import org.vorpal.research.kex.state.transformer.DescriptorGenerator
import org.vorpal.research.kex.trace.symbolic.*
import org.vorpal.research.kex.util.asmString
import org.vorpal.research.kex.util.javaString
import org.vorpal.research.kfg.Package
import org.vorpal.research.kfg.ir.*
import org.vorpal.research.kfg.ir.value.instruction.CallInst
import org.vorpal.research.kfg.ir.value.instruction.Instruction
import org.vorpal.research.kfg.ir.value.instruction.ReturnInst
import org.vorpal.research.kthelper.assert.unreachable
import org.vorpal.research.kthelper.logging.log
import java.util.*
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
    private val cache = WeakHashMap<TestChromosome, SymbolicState>()
    private val clauseSelector = ScoreGuidedClauseSelector(ctx.cm[Properties.TARGET_CLASS.asmString].allMethods, ctx)

    private val Method.isTargetMethod: Boolean
        get() = klass.fullName.javaString == Properties.TARGET_CLASS

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
                    updateWithTrace(observer.callTraces)
                    cache[test] = observer.state
                } catch (e: Throwable) {
                    logger.error("Error occurred while running test:\n{}", test, e)
                }
            }
        }
    }

    private suspend fun updateWithTrace(callTraces: List<List<Instruction>>) {
        for (trace in callTraces) {
            if (!trace.first().parent.method.isTargetMethod) continue
            clauseSelector.addExecutionTrace(trace)
        }
    }

    fun generateTest(): TestCase? = runBlocking {
        logger.info("Generating test with kex")

        val chosenTest = chooseTestCase()
        val prevState = cache[chosenTest]!!
        clauseSelector.setState(prevState.clauses.state, prevState.path.path)
        val (clauseList, pathList) = clauseSelector.next()

        val reversed = clauseSelector.reverse(pathList.last())!!
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

    private fun buildPrimitiveTermList(result: SMTModel) =
        result.assignments.keys.filter { term -> term.name.contains("primitive") }.sortedBy { term -> term.name }

    private fun generateTest(oldTest: TestCase, result: SMTModel): TestCase? {
        val primitiveTerms = buildPrimitiveTermList(result)
        if (primitiveTerms.isEmpty()) return null

        var isTestChanged = false
        val newTest = DefaultTestCase()
        var indexOfCurrentPrimitiveTerm = 0

        val descriptorGenerator = DescriptorGenerator(buildMethod(), ctx, result, InitialDescriptorReanimator(result, ctx))
        descriptorGenerator.generateAll()

        for (s in oldTest) {
            if (s is PrimitiveStatement<*>) {
                if (indexOfCurrentPrimitiveTerm == primitiveTerms.size) {
                    return null
                }
                isTestChanged = true
                when (s) {
                    is IntPrimitiveStatement -> {
                        s.value = (descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]
                                as ConstantDescriptor.Int).value
                    }

                    is LongPrimitiveStatement -> {
                        s.value = (descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]
                                as ConstantDescriptor.Long).value
                    }

                    is FloatPrimitiveStatement -> {
                        s.value = (descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]
                                as ConstantDescriptor.Float).value
                    }

                    is DoublePrimitiveStatement -> {
                        s.value = (descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]
                                as ConstantDescriptor.Double).value
                    }

                    is StringPrimitiveStatement -> {
                        s.value = descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]!!.asStringValue
                    }

                    is ShortPrimitiveStatement -> {
                        s.value = (descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]
                                as ConstantDescriptor.Short).value
                    }

                    is BytePrimitiveStatement -> {
                        s.value = (descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]
                                as ConstantDescriptor.Byte).value
                    }

                    is CharPrimitiveStatement -> {
                        s.value = (descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]
                                as ConstantDescriptor.Char).value
                    }

                    is BooleanPrimitiveStatement -> {
                        s.value = (descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]
                                as ConstantDescriptor.Bool).value
                    }

                    else -> unreachable {}
                }
                indexOfCurrentPrimitiveTerm++
            }
            newTest.addStatement(s)
        }

        if (isTestChanged)
            return newTest
        return null
    }

    private fun chooseTestCase(): TestChromosome {
        var chosenTest: TestChromosome
        do {
            chosenTest = cache.keys.random()
        } while (cache[chosenTest] == null || cache[chosenTest]!!.path.path.isEmpty())
        return chosenTest
    }

    private fun buildMethod(): Method {
        val cm = KexService.ctx.cm
        val klass: Class = OuterClass(cm, Package(""), "TestClass", Modifiers(0))
        val testDescriptor = MethodDescriptor(emptyList(), cm.type.voidType)
        return Method(cm, klass, "name", testDescriptor)
    }

    val Descriptor.asStringValue: String?
        get() = (this as? ObjectDescriptor)?.let { obj ->
            val valueDescriptor = obj["value", KexChar.asArray()] as? ArrayDescriptor
            valueDescriptor?.let { array ->
                (0 until array.length).map {
                    when (val value = array.elements.getOrDefault(it, descriptor { const(' ') })) {
                        is ConstantDescriptor.Char -> value.value
                        is ConstantDescriptor.Byte -> value.value.toInt().toChar()
                        else -> unreachable { log.error("Unexpected element type in string: $value") }
                    }
                }.joinToString("")
            }
        }
}