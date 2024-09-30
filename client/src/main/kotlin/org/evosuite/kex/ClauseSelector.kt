package org.evosuite.kex

import org.vorpal.research.kex.asm.analysis.util.SuspendableIterator
import org.vorpal.research.kex.trace.symbolic.Clause
import org.vorpal.research.kex.trace.symbolic.PathClause
import org.vorpal.research.kfg.ir.Method
import org.vorpal.research.kfg.ir.value.instruction.Instruction

interface ClauseSelector : SuspendableIterator<Pair<List<Clause>?, List<PathClause>?>> {
    val targets: Set<Method>

    suspend fun isEmpty(): Boolean
    suspend fun addExecutionTrace(
        trace: List<Instruction>
    )

    fun reverse(pathClause: PathClause): PathClause?
}
