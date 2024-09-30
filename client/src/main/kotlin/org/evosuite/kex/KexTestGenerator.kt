package org.evosuite.kex

import com.jetbrains.rd.util.first
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
import org.evosuite.testcase.statements.EnumPrimitiveStatement
import org.evosuite.testcase.statements.FunctionalMockStatement
import org.evosuite.testcase.statements.NullStatement
import org.evosuite.testcase.statements.PrimitiveStatement
import org.evosuite.testcase.statements.StringPrimitiveStatement
import org.evosuite.testcase.statements.environment.EnvironmentDataStatement
import org.evosuite.testcase.statements.numeric.*
import org.slf4j.LoggerFactory
import org.vorpal.research.kex.descriptor.*
import org.vorpal.research.kex.ktype.KexChar
import org.vorpal.research.kex.ktype.asArray
import org.vorpal.research.kex.smt.InitialDescriptorReanimator
import org.vorpal.research.kex.smt.SMTModel
import org.vorpal.research.kex.state.term.StaticClassRefTerm
import org.vorpal.research.kex.state.term.ValueTerm
import org.vorpal.research.kex.state.transformer.DescriptorGenerator
import org.vorpal.research.kex.trace.symbolic.PersistentClauseList
import org.vorpal.research.kex.trace.symbolic.PersistentPathCondition
import org.vorpal.research.kex.trace.symbolic.PersistentSymbolicState
import org.vorpal.research.kex.trace.symbolic.SymbolicState
import org.vorpal.research.kex.util.asmString
import org.vorpal.research.kex.util.javaString
import org.vorpal.research.kfg.Package
import org.vorpal.research.kfg.ir.*
import org.vorpal.research.kfg.ir.value.instruction.Instruction
import org.vorpal.research.kthelper.assert.unreachable
import org.vorpal.research.kthelper.logging.log
import java.util.*
import kotlin.time.ExperimentalTime

@ExperimentalTime
@InternalSerializationApi
@ExperimentalSerializationApi
@DelicateCoroutinesApi
object KexTestGenerator {
    private val logger = LoggerFactory.getLogger(KexTestGenerator::class.java)

    private val ctx get() = KexService.ctx
    private val cache = HashMap<String, SymbolicState>()
    private val clauseSelector =
        ScoreGuidedClauseSelector(ctx.cm[Properties.TARGET_CLASS.asmString].allMethods, ctx)

    private val Method.isTargetMethod: Boolean
        get() = klass.fullName.javaString == Properties.TARGET_CLASS

    const val KEX_GENERATION_TIMEOUT = 5000
    const val KEX_EXECUTION_TIMEOUT = 5000

    private fun isSupported(testCase: TestCase): Int {
        for (statement in testCase.toList()) {
            if (statement is FunctionalMockStatement) {
                return 0
            }
            if (statement is EnvironmentDataStatement<*>) {
                return 1
            }
        }
        return 2
    }

    fun collectTraces(testChromosomes: List<TestChromosome>, stoppingCondition: () -> Boolean) {
        runBlocking {
            logger.info("Trace collection")
            for (test in testChromosomes) {
                if (stoppingCondition()) break
                if (test.testCase.toCode() in cache) continue
                if (isSupported(test.testCase) != 2) continue

                try {
                    val observer = KexTestObserver(ctx)
                    val testCaseClone = test.testCase.clone() as DefaultTestCase
                    KexService.execute(testCaseClone, observer)
                    updateWithTrace(observer.callTraces)
                    cache[test.testCase.toCode()] = observer.state
                } catch (e: Throwable) {
                    logger.error("Error occurred while running test:\n{}", test, e)
                }
            }
        }
    }

    private suspend fun updateWithTrace(callTraces: List<List<Instruction>>) {
        for (trace in callTraces) {
            if (trace.isEmpty()) {
                continue
            }
            if (!trace.first().parent.method.isTargetMethod) continue
            clauseSelector.addExecutionTrace(trace)
        }
    }

    fun generateTest(chosenTest: TestChromosome, stoppingCondition: () -> Boolean): TestCase? = runBlocking {
        logger.info("Generating test with kex")

        val supported = isSupported(chosenTest.testCase)
        if (supported != 2) {
            TestChromosome.numberOfUnsupported[supported] += 1
            return@runBlocking null
        }

        var prevState = cache[chosenTest.testCase.toCode()]
        if (prevState == null) {
            collectTraces(listOf(chosenTest), stoppingCondition)
            prevState = cache[chosenTest.testCase.toCode()] ?: return@runBlocking null
        } else {
            TestChromosome.numberOfCollected += 1
        }
        clauseSelector.setState(prevState)

        if (clauseSelector.size() == 0) {
            TestChromosome.numberOfIrreversibleConcolic += 1
        } else if (!clauseSelector.hasNext()){
            TestChromosome.numberOfCovered += 1
        }

        var i = 0
        while (clauseSelector.hasNext() && !stoppingCondition()) {
            i += 1
            val (clauseList, pathList) = clauseSelector.next()
            if (clauseList == null || pathList == null) {
                break
            }

            val reversed = clauseSelector.reverse(pathList.last()) ?: continue
            clauseList[clauseList.size - 1] = reversed
            pathList[pathList.size - 1] = reversed

            val state = PersistentSymbolicState(
                PersistentClauseList(clauseList.toPersistentList()),
                PersistentPathCondition(pathList.toPersistentList()),
                prevState.concreteTypes.toPersistentMap(),
                prevState.concreteValues.toPersistentMap(),
                prevState.termMap.toPersistentMap()
            )

            if (i == 1)
                TestChromosome.numberOfKexCalls += 1

            val t = System.currentTimeMillis()
            val result = state.check(ctx)
            val duration = (System.currentTimeMillis() - t).toInt()
            if (result == null) {
                TestChromosome.timeOfUnsat += duration
                TestChromosome.numberOfUnsat += 1
                break
            } else {
                TestChromosome.timeOfSat += duration
                TestChromosome.numberOfSat += 1
            }
            val test = generateTest(chosenTest.testCase.clone(), result) ?: continue
            return@runBlocking test
        }
        if (stoppingCondition()) {
            TestChromosome.numberOfTimeouts += 1
        }
        logger.info("Unsuccessful in the test generation")
        null
    }.also {
        logger.debug("Kex produce new test:\n{}", it)
    }

    private fun buildPrimitiveTermList(result: SMTModel) =
        result.assignments.keys.filter { term -> term.name.contains("primitive") && term is ValueTerm }

    private fun generateTest(oldTest: TestCase, result: SMTModel): TestCase? {
        val primitiveTerms = buildPrimitiveTermList(result)

        var isTestChanged = false
        val newTest = DefaultTestCase()
        var indexOfCurrentPrimitiveTerm = 0
        var primitivesLeft = primitiveTerms.isNotEmpty()

        val descriptorGenerator =
            DescriptorGenerator(buildMethod(), ctx, result, InitialDescriptorReanimator(result, ctx))
        descriptorGenerator.generateAll()

        for (s in oldTest) {
            newTest.addStatement(s.clone(newTest))
            if (s is PrimitiveStatement<*> && s !is NullStatement && primitivesLeft) {
                isTestChanged = true
                when (s) {
                    is IntPrimitiveStatement -> {
                        (newTest.getStatement(newTest.size() - 1) as IntPrimitiveStatement)
                            .value = (descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]
                                as ConstantDescriptor.Int).value
                    }

                    is LongPrimitiveStatement -> {
                        (newTest.getStatement(newTest.size() - 1) as LongPrimitiveStatement)
                            .value = (descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]
                                as ConstantDescriptor.Long).value
                    }

                    is FloatPrimitiveStatement -> {
                        (newTest.getStatement(newTest.size() - 1) as FloatPrimitiveStatement)
                            .value = (descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]
                                as ConstantDescriptor.Float).value
                    }

                    is DoublePrimitiveStatement -> {
                        (newTest.getStatement(newTest.size() - 1) as DoublePrimitiveStatement)
                            .value = (descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]
                                as ConstantDescriptor.Double).value
                    }

                    is StringPrimitiveStatement -> {
                        (newTest.getStatement(newTest.size() - 1) as StringPrimitiveStatement)
                            .value = descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]!!
                                .asStringValue
                    }

                    is ShortPrimitiveStatement -> {
                        (newTest.getStatement(newTest.size() - 1) as ShortPrimitiveStatement)
                            .value = (descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]
                                as ConstantDescriptor.Short).value
                    }

                    is BytePrimitiveStatement -> {
                        (newTest.getStatement(newTest.size() - 1) as BytePrimitiveStatement)
                            .value = (descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]
                                as ConstantDescriptor.Byte).value
                    }

                    is CharPrimitiveStatement -> {
                        (newTest.getStatement(newTest.size() - 1) as CharPrimitiveStatement)
                            .value = (descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]
                                as ConstantDescriptor.Char).value
                    }

                    is BooleanPrimitiveStatement -> {
                        (newTest.getStatement(newTest.size() - 1) as BooleanPrimitiveStatement)
                            .value = (descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]]
                                as ConstantDescriptor.Bool).value
                    }

                    is EnumPrimitiveStatement<*> -> {
                        val descriptor = (descriptorGenerator.memory[primitiveTerms[indexOfCurrentPrimitiveTerm]] as ObjectDescriptor)
                        val classTerm = descriptorGenerator.memory.filter {
                            entry -> entry.key is StaticClassRefTerm && entry.key.type == descriptor.klass
                        }
                        assert(classTerm.size == 1)
                        val value = (classTerm.first().value as ClassDescriptor).fields.filter {
                            entry -> entry.value.term == descriptor.term
                        }
                        assert(value.size == 1)
                        val enumValue = s.enumValues.find { v -> v.name == value.first().key.first }
                        (newTest.getStatement(newTest.size() - 1) as EnumPrimitiveStatement<*>).value = enumValue
                    }

                    else -> unreachable {}
                }
                indexOfCurrentPrimitiveTerm++
                if (indexOfCurrentPrimitiveTerm == primitiveTerms.size) {
                    primitivesLeft = false
                }
            }
        }

        if (isTestChanged)
            return newTest
        return null
    }

    private fun buildMethod(): Method {
        val cm = KexService.ctx.cm
        val klass: Class = OuterClass(cm, Package(""), "TestClass", Modifiers(0))
        val testDescriptor = MethodDescriptor(emptyList(), cm.type.voidType)
        return Method(cm, klass, "name", testDescriptor)
    }

    private val Descriptor.asStringValue: String?
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