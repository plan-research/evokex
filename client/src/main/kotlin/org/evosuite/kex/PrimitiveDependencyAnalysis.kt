package org.evosuite.kex

import org.vorpal.research.kex.state.predicate.*
import org.vorpal.research.kex.state.term.*
import org.vorpal.research.kex.state.transformer.Transformer
import java.util.*

class PrimitiveDependencyAnalysis : Transformer<PrimitiveDependencyAnalysis> {
    private val isPrimitiveDependentTerm = WeakHashMap<Term, Boolean>()
    private val isPrimitiveDependentPathPredicate = mutableListOf<Boolean>()

    init {
        isPrimitiveDependentTerm[ConstBoolTerm(true)] = false
        isPrimitiveDependentTerm[ConstBoolTerm(false)] = false
    }

    fun isPrimitiveDependentPathPredicate(index: Int): Boolean {
        assert(isPrimitiveDependentPathPredicate.size >= index)
        return isPrimitiveDependentPathPredicate[index]
    }

    private val Term.isPrimitiveValue: Boolean get() = this.name.contains("%primitive%")

    ////////////////////////////////////////////////////////////////////
    // Term
    ////////////////////////////////////////////////////////////////////

    override fun transformArrayLoadTerm(term: ArrayLoadTerm): Term {
        assert(term.arrayRef is ArrayIndexTerm)
        isPrimitiveDependentTerm[term] =
            isPrimitiveDependentTerm[term.arrayRef]!! || isPrimitiveDependentTerm[(term.arrayRef as ArrayIndexTerm).arrayRef]!!
        return term
    }

    override fun transformArrayContainsTerm(term: ArrayContainsTerm): Term {
        isPrimitiveDependentTerm[term] =
            isPrimitiveDependentTerm[term.value]!! || isPrimitiveDependentTerm[term.array]!!
        return term
    }

    override fun transformArrayIndexTerm(term: ArrayIndexTerm): Term {
        isPrimitiveDependentTerm[term] =
            isPrimitiveDependentTerm[term.index]!! || isPrimitiveDependentTerm[term.arrayRef]!!
        return term
    }

    override fun transformArgumentTerm(term: ArgumentTerm): Term {
        error("Should not transform ArgumentTerm")
    }

    override fun transformArrayLengthTerm(term: ArrayLengthTerm): Term {
        isPrimitiveDependentTerm[term] = false
        return term
    }

    override fun transformCharAtTerm(term: CharAtTerm): Term {
        isPrimitiveDependentTerm[term] =
            isPrimitiveDependentTerm[term.index]!! || isPrimitiveDependentTerm[term.string]!!
        return term
    }

    override fun transformBinaryTerm(term: BinaryTerm): Term {
        isPrimitiveDependentTerm[term] = isPrimitiveDependentTerm[term.lhv]!! || isPrimitiveDependentTerm[term.rhv]!!
        return term
    }

    override fun transformBoundTerm(term: BoundTerm): Term {
        isPrimitiveDependentTerm[term] = false
        return term
    }

    override fun transformCallTerm(term: CallTerm): Term {
        isPrimitiveDependentTerm[term] = term.arguments.fold(false) { acc, cur ->
            isPrimitiveDependentTerm[cur]!! || acc
        } || isPrimitiveDependentTerm[term.owner]!!
        return term
    }

    override fun transformCastTerm(term: CastTerm): Term {
        isPrimitiveDependentTerm[term] = isPrimitiveDependentTerm[term.operand]
        return term
    }

    override fun transformClassAccessTerm(term: ClassAccessTerm): Term {
        isPrimitiveDependentTerm[term] = isPrimitiveDependentTerm[term.operand]
        return term
    }

    override fun transformCmpTerm(term: CmpTerm): Term {
        if (term.rhv !is NullTerm) {
            isPrimitiveDependentTerm[term] =
                isPrimitiveDependentTerm[term.lhv]!! || isPrimitiveDependentTerm[term.rhv]!!
        } else {
            isPrimitiveDependentTerm[term] = false
        }
        return term
    }

    override fun transformConcatTerm(term: ConcatTerm): Term {
        isPrimitiveDependentTerm[term] = isPrimitiveDependentTerm[term.lhv]!! || isPrimitiveDependentTerm[term.rhv]!!
        return term
    }

    override fun transformConstBoolTerm(term: ConstBoolTerm): Term {
        isPrimitiveDependentTerm[term] = false
        return term
    }

    override fun transformConstByteTerm(term: ConstByteTerm): Term {
        isPrimitiveDependentTerm[term] = false
        return term
    }

    override fun transformConstCharTerm(term: ConstCharTerm): Term {
        isPrimitiveDependentTerm[term] = false
        return term
    }

    override fun transformConstDoubleTerm(term: ConstDoubleTerm): Term {
        isPrimitiveDependentTerm[term] = false
        return term
    }

    override fun transformConstIntTerm(term: ConstIntTerm): Term {
        isPrimitiveDependentTerm[term] = false
        return term
    }

    override fun transformConstLongTerm(term: ConstLongTerm): Term {
        isPrimitiveDependentTerm[term] = false
        return term
    }

    override fun transformConstFloatTerm(term: ConstFloatTerm): Term {
        isPrimitiveDependentTerm[term] = false
        return term
    }

    override fun transformConstClassTerm(term: ConstClassTerm): Term {
        isPrimitiveDependentTerm[term] = false
        return term
    }

    override fun transformConstStringTerm(term: ConstStringTerm): Term {
        isPrimitiveDependentTerm[term] = false
        return term
    }

    override fun transformConstShortTerm(term: ConstShortTerm): Term {
        isPrimitiveDependentTerm[term] = false
        return term
    }

    override fun transformEndsWithTerm(term: EndsWithTerm): Term {
        isPrimitiveDependentTerm[term] =
            isPrimitiveDependentTerm[term.string]!! || isPrimitiveDependentTerm[term.suffix]!!
        return term
    }

    override fun transformEqualsTerm(term: EqualsTerm): Term {
        isPrimitiveDependentTerm[term] = isPrimitiveDependentTerm[term.lhv]!! || isPrimitiveDependentTerm[term.rhv]!!
        return term
    }

    override fun transformExistsTerm(term: ExistsTerm): Term {
        isPrimitiveDependentTerm[term] =
            isPrimitiveDependentTerm[term.start]!! || isPrimitiveDependentTerm[term.end]!! || isPrimitiveDependentTerm[term.body]!!
        return term
    }

    override fun transformFieldLoadTerm(term: FieldLoadTerm): Term {
        isPrimitiveDependentTerm[term] = isPrimitiveDependentTerm[term.field]
        return term
    }

    override fun transformFieldTerm(term: FieldTerm): Term {
        return term
    }

    override fun transformForAllTerm(term: ForAllTerm): Term {
        isPrimitiveDependentTerm[term] =
            isPrimitiveDependentTerm[term.start]!! || isPrimitiveDependentTerm[term.end]!! || isPrimitiveDependentTerm[term.body]!!
        return term
    }

    override fun transformIndexOfTerm(term: IndexOfTerm): Term {
        isPrimitiveDependentTerm[term] =
            isPrimitiveDependentTerm[term.string]!! || isPrimitiveDependentTerm[term.substring]!! || isPrimitiveDependentTerm[term.offset]!!
        return term
    }

    override fun transformInstanceOfTerm(term: InstanceOfTerm): Term {
        isPrimitiveDependentTerm[term] = false
        return term
    }

    override fun transformIteTerm(term: IteTerm): Term {
        isPrimitiveDependentTerm[term] =
            isPrimitiveDependentTerm[term.cond]!! || isPrimitiveDependentTerm[term.trueValue]!! || isPrimitiveDependentTerm[term.falseValue]!!
        return term
    }

    override fun transformLambdaTerm(term: LambdaTerm): Term {
        isPrimitiveDependentTerm[term] = term.parameters.fold(false) { acc, cur ->
            isPrimitiveDependentTerm[cur]!! || acc
        }
        return term
    }

    override fun transformNegTerm(term: NegTerm): Term {
        isPrimitiveDependentTerm[term] = isPrimitiveDependentTerm[term.operand]
        return term
    }

    override fun transformNullTerm(term: NullTerm): Term {
        isPrimitiveDependentTerm[term] = false
        return term
    }

    override fun transformReturnValueTerm(term: ReturnValueTerm): Term {
        isPrimitiveDependentTerm[term] = false
        return term
    }

    override fun transformStartsWithTerm(term: StartsWithTerm): Term {
        isPrimitiveDependentTerm[term] =
            isPrimitiveDependentTerm[term.string]!! || isPrimitiveDependentTerm[term.prefix]!!
        return term
    }

    override fun transformStaticClassRefTerm(term: StaticClassRefTerm): Term {
        isPrimitiveDependentTerm[term] = false
        return term
    }

    override fun transformStringContainsTerm(term: StringContainsTerm): Term {
        isPrimitiveDependentTerm[term] =
            isPrimitiveDependentTerm[term.string]!! || isPrimitiveDependentTerm[term.substring]!!
        return term
    }

    override fun transformStringLengthTerm(term: StringLengthTerm): Term {
        isPrimitiveDependentTerm[term] = isPrimitiveDependentTerm[term.string]
        return term
    }

    override fun transformStringParseTerm(term: StringParseTerm): Term {
        isPrimitiveDependentTerm[term] = isPrimitiveDependentTerm[term.string]
        return term
    }

    override fun transformSubstringTerm(term: SubstringTerm): Term {
        isPrimitiveDependentTerm[term] =
            isPrimitiveDependentTerm[term.string]!! || isPrimitiveDependentTerm[term.offset]!! || isPrimitiveDependentTerm[term.length]!!
        return term
    }

    override fun transformToStringTerm(term: ToStringTerm): Term {
        isPrimitiveDependentTerm[term] = isPrimitiveDependentTerm[term.value]
        return term
    }

    override fun transformUndefTerm(term: UndefTerm): Term {
        isPrimitiveDependentTerm[term] = false
        return term
    }

    override fun transformValueTerm(term: ValueTerm): Term {
        if (term.isPrimitiveValue) isPrimitiveDependentTerm[term] = true
        if (isPrimitiveDependentTerm[term] == null) isPrimitiveDependentTerm[term] = false
        return term
    }

    ////////////////////////////////////////////////////////////////////
    // Predicate
    ////////////////////////////////////////////////////////////////////

    override fun transformArrayInitializerPredicate(predicate: ArrayInitializerPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += isPrimitiveDependentTerm[predicate.arrayRef]!! || isPrimitiveDependentTerm[predicate.value]!!
        } else {
            assert(predicate.arrayRef is ArrayIndexTerm)
            isPrimitiveDependentTerm[(predicate.arrayRef as ArrayIndexTerm).arrayRef] =
                isPrimitiveDependentTerm[predicate.value]!!
            isPrimitiveDependentTerm[predicate.arrayRef] = isPrimitiveDependentTerm[predicate.value]!!
        }
        return predicate
    }

    override fun transformArrayStorePredicate(predicate: ArrayStorePredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += isPrimitiveDependentTerm[predicate.arrayRef]!! || isPrimitiveDependentTerm[predicate.value]!!
        } else {
            assert(predicate.arrayRef is ArrayIndexTerm)
            isPrimitiveDependentTerm[(predicate.arrayRef as ArrayIndexTerm).arrayRef] =
                isPrimitiveDependentTerm[predicate.value]!!
            isPrimitiveDependentTerm[predicate.arrayRef] = isPrimitiveDependentTerm[predicate.value]!!
        }
        return predicate
    }

    override fun transformBoundStorePredicate(predicate: BoundStorePredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        }
        return predicate
    }

    override fun transformCallPredicate(predicate: CallPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += isPrimitiveDependentTerm[predicate.lhv]!! || isPrimitiveDependentTerm[predicate.callTerm]!!
        } else {
            if (predicate.hasLhv)
                isPrimitiveDependentTerm[predicate.lhv] = isPrimitiveDependentTerm[predicate.callTerm]
        }
        return predicate
    }

    override fun transformCatchPredicate(predicate: CatchPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        }
        return predicate
    }

    override fun transformDefaultSwitchPredicate(predicate: DefaultSwitchPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        }
        return predicate
    }

    override fun transformEnterMonitorPredicate(predicate: EnterMonitorPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        }
        return predicate
    }

    override fun transformEqualityPredicate(predicate: EqualityPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += isPrimitiveDependentTerm[predicate.lhv]!! || isPrimitiveDependentTerm[predicate.rhv]!!
        } else {
            if (predicate.lhv !is ConstBoolTerm) {
                isPrimitiveDependentTerm[predicate.lhv] = isPrimitiveDependentTerm[predicate.rhv]
            }
        }
        return predicate
    }

    override fun transformExitMonitorPredicate(predicate: ExitMonitorPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        }
        return predicate
    }

    override fun transformFieldInitializerPredicate(predicate: FieldInitializerPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += isPrimitiveDependentTerm[predicate.field]!! || isPrimitiveDependentTerm[predicate.field]!! || isPrimitiveDependentTerm[predicate.value]!!
        } else {
            isPrimitiveDependentTerm[predicate.field] = isPrimitiveDependentTerm[predicate.value]
        }
        return predicate
    }

    override fun transformFieldStorePredicate(predicate: FieldStorePredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += isPrimitiveDependentTerm[predicate.field]!! || isPrimitiveDependentTerm[predicate.value]!!
        } else {
            isPrimitiveDependentTerm[predicate.field] = isPrimitiveDependentTerm[predicate.value]
        }
        return predicate
    }

    override fun transformGenerateArrayPredicate(predicate: GenerateArrayPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += isPrimitiveDependentTerm[predicate.lhv]!! || isPrimitiveDependentTerm[predicate.length]!! || isPrimitiveDependentTerm[predicate.generator]!!
        } else {
            isPrimitiveDependentTerm[predicate.lhv] =
                isPrimitiveDependentTerm[predicate.length]!! || isPrimitiveDependentTerm[predicate.generator]!!
        }
        return predicate
    }

    override fun transformInequalityPredicate(predicate: InequalityPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        }
        return predicate
    }

    override fun transformNewArrayInitializerPredicate(predicate: NewArrayInitializerPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += isPrimitiveDependentTerm[predicate.lhv]!! || predicate.elements.fold(
                false
            ) { acc, cur ->
                isPrimitiveDependentTerm[cur]!! || acc
            } || isPrimitiveDependentTerm[predicate.length]!!
        } else {
            isPrimitiveDependentTerm[predicate.lhv] = predicate.elements.fold(false) { acc, cur ->
                isPrimitiveDependentTerm[cur]!! || acc
            } || isPrimitiveDependentTerm[predicate.length]!!
        }
        return predicate
    }

    override fun transformNewArrayPredicate(predicate: NewArrayPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += isPrimitiveDependentTerm[predicate.lhv]!! || predicate.dimensions.fold(
                false
            ) { acc, cur ->
                isPrimitiveDependentTerm[cur]!! || acc
            }
        } else {
            isPrimitiveDependentTerm[predicate.lhv] = predicate.dimensions.fold(false) { acc, cur ->
                isPrimitiveDependentTerm[cur]!! || acc
            }
        }
        return predicate
    }

    override fun transformNewInitializerPredicate(predicate: NewInitializerPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        }
        return predicate
    }

    override fun transformNewPredicate(predicate: NewPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        }
        return predicate
    }

    override fun transformThrowPredicate(predicate: ThrowPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        }
        return predicate
    }
}