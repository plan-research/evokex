package org.evosuite.kex

import kotlinx.collections.immutable.toPersistentList
import org.vorpal.research.kex.ExecutionContext
import org.vorpal.research.kex.asm.analysis.concolic.bfs.BfsPathSelectorImpl
import org.vorpal.research.kex.asm.analysis.concolic.coverage.InstructionGraph
import org.vorpal.research.kex.state.predicate.*
import org.vorpal.research.kex.state.term.*
import org.vorpal.research.kex.trace.symbolic.Clause
import org.vorpal.research.kex.trace.symbolic.PathClause
import org.vorpal.research.kex.trace.symbolic.PathClauseType
import org.vorpal.research.kfg.Package
import org.vorpal.research.kfg.ir.Method
import org.vorpal.research.kfg.ir.MethodDescriptor
import org.vorpal.research.kfg.ir.Modifiers
import org.vorpal.research.kfg.ir.OuterClass
import org.vorpal.research.kfg.ir.value.instruction.*
import java.util.*

class ScoreGuidedClauseSelector(
    override val targets: Set<Method>,
    private val ctx: ExecutionContext
) : ClauseSelector {
    private val instructionGraph = InstructionGraph(targets)
    private val clauses = mutableListOf<Clause>()
    private val path = mutableListOf<PathClause>()
    private val candidates = mutableListOf<Pair<Int, Int>>()
    private val isPrimitiveDependent = WeakHashMap<Term, Boolean>()
    private val isCallPrimitiveDependent = mutableListOf(false)
    private val targetInstructions = targets.flatMapTo(mutableSetOf()) { it.body.flatten() }
    private val coveredInstructions = mutableSetOf<Instruction>()
    private var index = 0

    fun allCovered() = coveredInstructions.containsAll(targetInstructions)

    override suspend fun isEmpty(): Boolean = allCovered() ||
            candidates.size == index

    override suspend fun hasNext(): Boolean = !isEmpty()

    fun size() = candidates.size

    override suspend fun next(): Pair<MutableList<Clause>?, MutableList<PathClause>?> {
        if (isEmpty()) return null to null
        val candidate = candidates[index]
        index += 1
        return clauses.take(candidate.first + 1).toMutableList() to path.take(candidate.second + 1).toMutableList()
    }

    override suspend fun addExecutionTrace(trace: List<Instruction>) {
        instructionGraph.addTrace(trace)
        coveredInstructions += trace
    }

    fun setState(newClauses: List<Clause>, newPath: List<PathClause>) {
        clauses.clear()
        path.clear()
        clauses.addAll(newClauses)
        path.addAll(newPath)

        candidates.clear()
        var pathIndex = 0
        val stackTraces = mutableListOf<List<Pair<Instruction?, Method>>>()
        val currentStackTrace = mutableListOf<Pair<Instruction?, Method>>()
        var previousInstruction: Instruction? = null
        for (i in clauses.indices) {
            val clause = clauses[i]
            val currentInstruction = clause.instruction
            try {
                val currentMethod = currentInstruction.parent.method
                when (currentInstruction) {
                    currentMethod.body.entry.first() -> {
                        currentStackTrace += previousInstruction to currentMethod
                        isCallPrimitiveDependent += false
                    }

                    is CallInst -> {
                        previousInstruction = currentInstruction
                    }

                    is ReturnInst -> {
                        currentStackTrace.removeAt(currentStackTrace.size - 1)
                        isCallPrimitiveDependent.removeAt(isCallPrimitiveDependent.size - 1)
                    }

                    is CatchInst -> {
                        while (stackTraces[stackTraces.size - 1].last().second != currentMethod) {
                            currentStackTrace.removeAt(currentStackTrace.size - 1)
                            isCallPrimitiveDependent.removeAt(isCallPrimitiveDependent.size - 1)
                        }
                    }
                }
            } catch (_: Exception) {
            }

            if (clause is PathClause) {
                stackTraces += currentStackTrace.toList()
                assert(clause == path[pathIndex])
                if (isPathClauseReversible(clause)) {
                    candidates.add(i to pathIndex)
                }
                pathIndex++
            } else {
                when (val predicate = clause.predicate) {
                    is FieldStorePredicate -> {
                        isPrimitiveDependent[predicate.field] = isPrimitive(predicate.value)
                        isCallPrimitiveDependent[isCallPrimitiveDependent.size - 1] =
                            isCallPrimitiveDependent[isCallPrimitiveDependent.size - 1] || isPrimitiveDependent[predicate.field]!!
                    }

                    is EqualityPredicate -> {
                        if (predicate.lhv !is ConstBoolTerm) {
                            isPrimitiveDependent[predicate.lhv] = isPrimitive(predicate.rhv)
                            if (predicate.lhv.isReturnValue) {
                                isPrimitiveDependent[predicate.lhv] =
                                    isPrimitiveDependent[predicate.lhv]!! || isCallPrimitiveDependent.last()
                            }
                            isCallPrimitiveDependent[isCallPrimitiveDependent.size - 1] =
                                isCallPrimitiveDependent[isCallPrimitiveDependent.size - 1] || isPrimitiveDependent[predicate.lhv]!!
                        }
                    }


                    is InequalityPredicate -> {
                        isPrimitiveDependent[predicate.lhv] = isPrimitive(predicate.rhv)
                        isCallPrimitiveDependent[isCallPrimitiveDependent.size - 1] =
                            isCallPrimitiveDependent[isCallPrimitiveDependent.size - 1] || isPrimitiveDependent[predicate.lhv]!!
                    }

                    is GenerateArrayPredicate -> {
                        isPrimitiveDependent[predicate.lhv] =
                            isPrimitive(predicate.length) || isPrimitive(predicate.generator)
                        isCallPrimitiveDependent[isCallPrimitiveDependent.size - 1] =
                            isCallPrimitiveDependent[isCallPrimitiveDependent.size - 1] || isPrimitiveDependent[predicate.lhv]!!
                    }

                    is FieldInitializerPredicate -> {
                        isPrimitiveDependent[predicate.field] = isPrimitive(predicate.value)
                        isCallPrimitiveDependent[isCallPrimitiveDependent.size - 1] =
                            isCallPrimitiveDependent[isCallPrimitiveDependent.size - 1] || isPrimitiveDependent[predicate.field]!!
                    }

                    is NewPredicate -> {
                        isPrimitiveDependent[predicate.lhv] = false
                    }

                    is NewInitializerPredicate -> {
                        isPrimitiveDependent[predicate.lhv] = false
                    }

                    is NewArrayPredicate -> {
                        isPrimitiveDependent[predicate.lhv] = false
                    }

                    is NewArrayInitializerPredicate -> {
                        isPrimitiveDependent[predicate.lhv] = false
                    }

                    is ArrayStorePredicate -> {
                        isPrimitiveDependent[predicate.arrayRef] = isPrimitive(predicate.value)
                        isCallPrimitiveDependent[isCallPrimitiveDependent.size - 1] =
                            isCallPrimitiveDependent[isCallPrimitiveDependent.size - 1] || isPrimitiveDependent[predicate.arrayRef]!!
                    }

                    is ArrayInitializerPredicate -> {
                        isPrimitiveDependent[predicate.arrayRef] = isPrimitive(predicate.value)
                        isCallPrimitiveDependent[isCallPrimitiveDependent.size - 1] =
                            isCallPrimitiveDependent[isCallPrimitiveDependent.size - 1] || isPrimitiveDependent[predicate.arrayRef]!!
                    }
                }
            }
        }

        index = 0
        assert(pathIndex == path.size)

        candidates.sortBy { (_, pathIndex) ->
            val distance = instructionGraph.getVertex(path[pathIndex].instruction)
                .distanceToUncovered(targets, stackTraces[pathIndex].toPersistentList()).first
            distance
        }
    }

    private fun isPathClauseReversible(clause: PathClause): Boolean {
        return clause.type == PathClauseType.CONDITION_CHECK && clause.predicate.operands.fold(false) { acc, cur ->
            acc || getOrUpdate(cur)
        }
    }

    // TODO: rewrite?
    override fun reverse(pathClause: PathClause): PathClause? = BfsPathSelectorImpl(
        ctx, Method(
            ctx.cm, OuterClass(ctx.cm, Package(""), "TestClass", Modifiers(0)), "name",
            MethodDescriptor(emptyList(), ctx.cm.type.voidType)
        )
    ).reverse(pathClause)

    private val Term.isPrimitiveValue: Boolean get() = this.name.contains("%primitive%")
    private val Term.isReturnValue: Boolean get() = this.name.contains("retval")

    private fun isPrimitive(term: Term): Boolean {
        when (term) {
            is CmpTerm -> {
                if (term.rhv !is NullTerm) {
                    return getOrUpdate(term.lhv) || getOrUpdate(term.rhv)
                }
                return false
            }

            is InstanceOfTerm -> return false

            is ValueTerm -> {
                if (term.isPrimitiveValue)
                    return true
                if (term.isReturnValue) {
                    if (isCallPrimitiveDependent.isEmpty()) return getOrUpdate(term, false)
                    return getOrUpdate(term, isCallPrimitiveDependent.last())
                }
                return isPrimitiveDependent[term] ?: false
            }

            else -> return term.subTerms.fold(false) { acc, cur -> acc || getOrUpdate(cur) }

        }
    }

    private fun getOrUpdate(term: Term, value: Boolean? = null): Boolean {
        if (isPrimitiveDependent[term] == null) {
            isPrimitiveDependent[term] = value ?: isPrimitive(term)
        }
        return isPrimitiveDependent[term]!!
    }

}
