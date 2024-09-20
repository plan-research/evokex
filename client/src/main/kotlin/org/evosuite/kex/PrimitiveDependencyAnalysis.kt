package org.evosuite.kex

import org.vorpal.research.kex.state.predicate.*
import org.vorpal.research.kex.state.term.*
import org.vorpal.research.kex.state.transformer.Transformer
import org.vorpal.research.kthelper.assert.unreachable
import java.util.*

class PrimitiveDependencyAnalysis : Transformer<PrimitiveDependencyAnalysis> {
    private val isPrimitiveDependent = WeakHashMap<Term, Boolean>()

    init {
        isPrimitiveDependent[ConstBoolTerm(true)] = false
        isPrimitiveDependent[ConstBoolTerm(false)] = false
    }

    fun isPrimitiveDependent(term: Term): Boolean {
        return isPrimitiveDependent[term] ?: unreachable { }
    }

    private val Term.isPrimitiveValue: Boolean get() = this.name.contains("%primitive%")

    ////////////////////////////////////////////////////////////////////
    // Term
    ////////////////////////////////////////////////////////////////////

    override fun transformArrayLoadTerm(term: ArrayLoadTerm): Term {
        assert(term.arrayRef is ArrayIndexTerm)
        isPrimitiveDependent[term] =
            isPrimitiveDependent[term.arrayRef]!! || isPrimitiveDependent[(term.arrayRef as ArrayIndexTerm).arrayRef]!!
        return term
    }

    override fun transformArrayContainsTerm(term: ArrayContainsTerm): Term {
        isPrimitiveDependent[term] = isPrimitiveDependent[term.value]!! || isPrimitiveDependent[term.array]!!
        return term
    }

    override fun transformArrayIndexTerm(term: ArrayIndexTerm): Term {
        isPrimitiveDependent[term] = isPrimitiveDependent[term.index]!! || isPrimitiveDependent[term.arrayRef]!!
        return term
    }

    override fun transformArgumentTerm(term: ArgumentTerm): Term {
        error("Should not transform ArgumentTerm")
    }

    override fun transformArrayLengthTerm(term: ArrayLengthTerm): Term {
        isPrimitiveDependent[term] = false
        return term
    }

    override fun transformCharAtTerm(term: CharAtTerm): Term {
        isPrimitiveDependent[term] = isPrimitiveDependent[term.index]!! || isPrimitiveDependent[term.string]!!
        return term
    }

    override fun transformBinaryTerm(term: BinaryTerm): Term {
        isPrimitiveDependent[term] = isPrimitiveDependent[term.lhv]!! || isPrimitiveDependent[term.rhv]!!
        return term
    }

    override fun transformBoundTerm(term: BoundTerm): Term {
        isPrimitiveDependent[term] = false
        return term
    }

    override fun transformCallTerm(term: CallTerm): Term {
        isPrimitiveDependent[term] = term.arguments.fold(false) { acc, cur ->
            isPrimitiveDependent[cur]!! || acc
        } || isPrimitiveDependent[term.owner]!!
        return term
    }

    override fun transformCastTerm(term: CastTerm): Term {
        isPrimitiveDependent[term] = isPrimitiveDependent[term.operand]
        return term
    }

    override fun transformClassAccessTerm(term: ClassAccessTerm): Term {
        isPrimitiveDependent[term] = isPrimitiveDependent[term.operand]
        return term
    }

    override fun transformCmpTerm(term: CmpTerm): Term {
        if (term.rhv !is NullTerm) {
            isPrimitiveDependent[term] = isPrimitiveDependent[term.lhv]!! || isPrimitiveDependent[term.rhv]!!
        } else {
            isPrimitiveDependent[term] = false
        }
        return term
    }

    override fun transformConcatTerm(term: ConcatTerm): Term {
        isPrimitiveDependent[term] = isPrimitiveDependent[term.lhv]!! || isPrimitiveDependent[term.rhv]!!
        return term
    }

    override fun transformConstBoolTerm(term: ConstBoolTerm): Term {
        isPrimitiveDependent[term] = false
        return term
    }

    override fun transformConstByteTerm(term: ConstByteTerm): Term {
        isPrimitiveDependent[term] = false
        return term
    }

    override fun transformConstCharTerm(term: ConstCharTerm): Term {
        isPrimitiveDependent[term] = false
        return term
    }

    override fun transformConstDoubleTerm(term: ConstDoubleTerm): Term {
        isPrimitiveDependent[term] = false
        return term
    }

    override fun transformConstIntTerm(term: ConstIntTerm): Term {
        isPrimitiveDependent[term] = false
        return term
    }

    override fun transformConstLongTerm(term: ConstLongTerm): Term {
        isPrimitiveDependent[term] = false
        return term
    }

    override fun transformConstFloatTerm(term: ConstFloatTerm): Term {
        isPrimitiveDependent[term] = false
        return term
    }

    override fun transformConstClassTerm(term: ConstClassTerm): Term {
        isPrimitiveDependent[term] = false
        return term
    }

    override fun transformConstStringTerm(term: ConstStringTerm): Term {
        isPrimitiveDependent[term] = false
        return term
    }

    override fun transformConstShortTerm(term: ConstShortTerm): Term {
        isPrimitiveDependent[term] = false
        return term
    }

    override fun transformEndsWithTerm(term: EndsWithTerm): Term {
        isPrimitiveDependent[term] = isPrimitiveDependent[term.string]!! || isPrimitiveDependent[term.suffix]!!
        return term
    }

    override fun transformEqualsTerm(term: EqualsTerm): Term {
        isPrimitiveDependent[term] = isPrimitiveDependent[term.lhv]!! || isPrimitiveDependent[term.rhv]!!
        return term
    }

    override fun transformExistsTerm(term: ExistsTerm): Term {
        isPrimitiveDependent[term] =
            isPrimitiveDependent[term.start]!! || isPrimitiveDependent[term.end]!! || isPrimitiveDependent[term.body]!!
        return term
    }

    override fun transformFieldLoadTerm(term: FieldLoadTerm): Term {
        isPrimitiveDependent[term] = isPrimitiveDependent[term.field]
        return term
    }

    override fun transformFieldTerm(term: FieldTerm): Term {
        return term
    }

    override fun transformForAllTerm(term: ForAllTerm): Term {
        isPrimitiveDependent[term] =
            isPrimitiveDependent[term.start]!! || isPrimitiveDependent[term.end]!! || isPrimitiveDependent[term.body]!!
        return term
    }

    override fun transformIndexOfTerm(term: IndexOfTerm): Term {
        isPrimitiveDependent[term] =
            isPrimitiveDependent[term.string]!! || isPrimitiveDependent[term.substring]!! || isPrimitiveDependent[term.offset]!!
        return term
    }

    override fun transformInstanceOfTerm(term: InstanceOfTerm): Term {
        isPrimitiveDependent[term] = false
        return term
    }

    override fun transformIteTerm(term: IteTerm): Term {
        isPrimitiveDependent[term] =
            isPrimitiveDependent[term.cond]!! || isPrimitiveDependent[term.trueValue]!! || isPrimitiveDependent[term.falseValue]!!
        return term
    }

    override fun transformLambdaTerm(term: LambdaTerm): Term {
        isPrimitiveDependent[term] = term.parameters.fold(false) { acc, cur ->
            isPrimitiveDependent[cur]!! || acc
        }
        return term
    }

    override fun transformNegTerm(term: NegTerm): Term {
        isPrimitiveDependent[term] = isPrimitiveDependent[term.operand]
        return term
    }

    override fun transformNullTerm(term: NullTerm): Term {
        isPrimitiveDependent[term] = false
        return term
    }

    override fun transformReturnValueTerm(term: ReturnValueTerm): Term {
        isPrimitiveDependent[term] = false
        return term
    }

    override fun transformStartsWithTerm(term: StartsWithTerm): Term {
        isPrimitiveDependent[term] = isPrimitiveDependent[term.string]!! || isPrimitiveDependent[term.prefix]!!
        return term
    }

    override fun transformStaticClassRefTerm(term: StaticClassRefTerm): Term {
        isPrimitiveDependent[term] = false
        return term
    }

    override fun transformStringContainsTerm(term: StringContainsTerm): Term {
        isPrimitiveDependent[term] = isPrimitiveDependent[term.string]!! || isPrimitiveDependent[term.substring]!!
        return term
    }

    override fun transformStringLengthTerm(term: StringLengthTerm): Term {
        isPrimitiveDependent[term] = isPrimitiveDependent[term.string]
        return term
    }

    override fun transformStringParseTerm(term: StringParseTerm): Term {
        isPrimitiveDependent[term] = isPrimitiveDependent[term.string]
        return term
    }

    override fun transformSubstringTerm(term: SubstringTerm): Term {
        isPrimitiveDependent[term] =
            isPrimitiveDependent[term.string]!! || isPrimitiveDependent[term.offset]!! || isPrimitiveDependent[term.length]!!
        return term
    }

    override fun transformToStringTerm(term: ToStringTerm): Term {
        isPrimitiveDependent[term] = isPrimitiveDependent[term.value]
        return term
    }

    override fun transformUndefTerm(term: UndefTerm): Term {
        isPrimitiveDependent[term] = false
        return term
    }

    override fun transformValueTerm(term: ValueTerm): Term {
        if (term.isPrimitiveValue) isPrimitiveDependent[term] = true
        if (isPrimitiveDependent[term] == null) isPrimitiveDependent[term] = false
        return term
    }

    ////////////////////////////////////////////////////////////////////
    // Predicate
    ////////////////////////////////////////////////////////////////////

    override fun transformArrayInitializerPredicate(predicate: ArrayInitializerPredicate): Predicate {
        assert(predicate.arrayRef is ArrayIndexTerm)
        isPrimitiveDependent[(predicate.arrayRef as ArrayIndexTerm).arrayRef] = isPrimitiveDependent[predicate.value]!!
        isPrimitiveDependent[predicate.arrayRef] = isPrimitiveDependent[predicate.value]!!
        return predicate
    }

    override fun transformArrayStorePredicate(predicate: ArrayStorePredicate): Predicate {
        assert(predicate.arrayRef is ArrayIndexTerm)
        isPrimitiveDependent[(predicate.arrayRef as ArrayIndexTerm).arrayRef] = isPrimitiveDependent[predicate.value]!!
        isPrimitiveDependent[predicate.arrayRef] = isPrimitiveDependent[predicate.value]!!
        return predicate
    }

    override fun transformBoundStorePredicate(predicate: BoundStorePredicate): Predicate {
        return predicate
    }

    override fun transformCallPredicate(predicate: CallPredicate): Predicate {
        if (predicate.hasLhv) isPrimitiveDependent[predicate.lhv] = isPrimitiveDependent[predicate.callTerm]
        return predicate
    }

    override fun transformCatchPredicate(predicate: CatchPredicate): Predicate {
        return predicate
    }

    override fun transformDefaultSwitchPredicate(predicate: DefaultSwitchPredicate): Predicate {
        return predicate
    }

    override fun transformEnterMonitorPredicate(predicate: EnterMonitorPredicate): Predicate {
        return predicate
    }

    override fun transformEqualityPredicate(predicate: EqualityPredicate): Predicate {
        if (predicate.lhv !is ConstBoolTerm) {
            isPrimitiveDependent[predicate.lhv] = isPrimitiveDependent[predicate.rhv]
        }
        return predicate
    }

    override fun transformExitMonitorPredicate(predicate: ExitMonitorPredicate): Predicate {
        return predicate
    }

    override fun transformFieldInitializerPredicate(predicate: FieldInitializerPredicate): Predicate {
        isPrimitiveDependent[predicate.field] = isPrimitiveDependent[predicate.value]
        return predicate
    }

    override fun transformFieldStorePredicate(predicate: FieldStorePredicate): Predicate {
        isPrimitiveDependent[predicate.field] = isPrimitiveDependent[predicate.value]
        return predicate
    }

    override fun transformGenerateArrayPredicate(predicate: GenerateArrayPredicate): Predicate {
        isPrimitiveDependent[predicate.lhv] =
            isPrimitiveDependent[predicate.length]!! || isPrimitiveDependent[predicate.generator]!!
        return predicate
    }

    override fun transformInequalityPredicate(predicate: InequalityPredicate): Predicate {
        return predicate
    }

    override fun transformNewArrayInitializerPredicate(predicate: NewArrayInitializerPredicate): Predicate {
        isPrimitiveDependent[predicate.lhv] = predicate.elements.fold(false) { acc, cur ->
            isPrimitiveDependent[cur]!! || acc
        } || isPrimitiveDependent[predicate.length]!!
        return predicate
    }

    override fun transformNewArrayPredicate(predicate: NewArrayPredicate): Predicate {
        isPrimitiveDependent[predicate.lhv] = predicate.dimensions.fold(false) { acc, cur ->
            isPrimitiveDependent[cur]!! || acc
        }
        return predicate
    }

    override fun transformNewInitializerPredicate(predicate: NewInitializerPredicate): Predicate {
        return predicate
    }

    override fun transformNewPredicate(predicate: NewPredicate): Predicate {
        return predicate
    }

    override fun transformThrowPredicate(predicate: ThrowPredicate): Predicate {
        return predicate
    }
}