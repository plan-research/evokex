package org.evosuite.kex

import kotlinx.collections.immutable.toPersistentList
import org.vorpal.research.kex.ExecutionContext
import org.vorpal.research.kex.asm.analysis.concolic.bfs.BfsPathSelectorImpl
import org.vorpal.research.kex.asm.analysis.concolic.coverage.InstructionGraph
import org.vorpal.research.kex.trace.symbolic.Clause
import org.vorpal.research.kex.trace.symbolic.PathClause
import org.vorpal.research.kfg.Package
import org.vorpal.research.kfg.ir.Method
import org.vorpal.research.kfg.ir.MethodDescriptor
import org.vorpal.research.kfg.ir.Modifiers
import org.vorpal.research.kfg.ir.OuterClass
import org.vorpal.research.kfg.ir.value.instruction.Instruction

class ScoreGuidedClauseSelector(
    override val targets: Set<Method>,
    private val ctx: ExecutionContext
) : ClauseSelector {
    private val instructionGraph = InstructionGraph(targets)
    private val instructionsGraph get() = instructionGraph
    private val clauses = mutableListOf<Clause>()
    private val path = mutableListOf<PathClause>()
    private val candidates = mutableListOf<Pair<Int, Int>>()
    private val targetInstructions = targets.flatMapTo(mutableSetOf()) { it.body.flatten() }
    private val coveredInstructions = mutableSetOf<Instruction>()

    override suspend fun isEmpty(): Boolean = coveredInstructions.containsAll(targetInstructions) ||
                                              candidates.isEmpty()

    override suspend fun hasNext(): Boolean = !isEmpty()

    override suspend fun next(): Pair<MutableList<Clause>, MutableList<PathClause>> {
        val candidate = candidates.random()
        candidates.remove(candidate)
        return clauses.take(candidate.first + 1).toMutableList() to path.take(candidate.second + 1).toMutableList()
    }

    override suspend fun addExecutionTrace(trace: List<Instruction>) {
        instructionsGraph.addTrace(trace)
        coveredInstructions += trace
    }

    suspend fun setState(newClauses: List<Clause>, newPath: List<PathClause>) {
        clauses.clear()
        path.clear()
        clauses.addAll(newClauses)
        path.addAll(newPath)

        candidates.clear()
        var pathIndex = 0
        for (i in clauses.indices) {
            if (clauses[i] is PathClause) {
                assert(clauses[i] == path[pathIndex])
                candidates.add(i to pathIndex)
                pathIndex++
            }
        }
        assert(pathIndex == path.size)
    }

    // TODO: rewrite?
    override fun reverse(pathClause: PathClause): PathClause? = BfsPathSelectorImpl(ctx, Method(
        ctx.cm, OuterClass(ctx.cm, Package(""), "TestClass", Modifiers(0)),"name",
        MethodDescriptor(emptyList(), ctx.cm.type.voidType)
    )).reverse(pathClause)

}
