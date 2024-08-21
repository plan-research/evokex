package org.evosuite.kex

import kotlinx.collections.immutable.toPersistentList
import org.vorpal.research.kex.ExecutionContext
import org.vorpal.research.kex.asm.analysis.concolic.bfs.BfsPathSelectorImpl
import org.vorpal.research.kex.asm.analysis.concolic.coverage.InstructionGraph
import org.vorpal.research.kex.trace.symbolic.Clause
import org.vorpal.research.kex.trace.symbolic.PathClause
import org.vorpal.research.kex.trace.symbolic.PathClauseType
import org.vorpal.research.kfg.Package
import org.vorpal.research.kfg.ir.Method
import org.vorpal.research.kfg.ir.MethodDescriptor
import org.vorpal.research.kfg.ir.Modifiers
import org.vorpal.research.kfg.ir.OuterClass
import org.vorpal.research.kfg.ir.value.instruction.CallInst
import org.vorpal.research.kfg.ir.value.instruction.CatchInst
import org.vorpal.research.kfg.ir.value.instruction.Instruction
import org.vorpal.research.kfg.ir.value.instruction.ReturnInst

class ScoreGuidedClauseSelector(
    override val targets: Set<Method>,
    private val ctx: ExecutionContext
) : ClauseSelector {
    private val instructionGraph = InstructionGraph(targets)
    private val clauses = mutableListOf<Clause>()
    private val path = mutableListOf<PathClause>()
    private val candidates = mutableListOf<Pair<Int, Int>>()
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
                    }

                    is CallInst -> {
                        previousInstruction = currentInstruction
                    }

                    is ReturnInst -> {
                        currentStackTrace.removeLast()
                    }

                    is CatchInst -> {
                        while (stackTraces[stackTraces.size - 1].last().second != currentMethod) {
                            currentStackTrace.removeLast()
                        }
                    }
                }
            } catch (_: Exception) {}

            if (clause is PathClause) {
                stackTraces += currentStackTrace.toList()
                assert(clause == path[pathIndex])
                if (clause.type == PathClauseType.CONDITION_CHECK)
                    candidates.add(i to pathIndex)
                pathIndex++
            }
        }

        index = 0
        assert(pathIndex == path.size)

        candidates.sortBy { (_, pathIndex) ->

            val distance = instructionGraph.getVertex(path[pathIndex].instruction).
                distanceToUncovered(targets, stackTraces[pathIndex].toPersistentList()).first

            distance
        }
    }

    // TODO: rewrite?
    override fun reverse(pathClause: PathClause): PathClause? = BfsPathSelectorImpl(ctx, Method(
        ctx.cm, OuterClass(ctx.cm, Package(""), "TestClass", Modifiers(0)),"name",
        MethodDescriptor(emptyList(), ctx.cm.type.voidType)
    )).reverse(pathClause)

}
