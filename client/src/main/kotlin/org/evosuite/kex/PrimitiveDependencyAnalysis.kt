package org.evosuite.kex

import org.vorpal.research.kex.state.predicate.*
import org.vorpal.research.kex.state.term.*
import org.vorpal.research.kex.state.transformer.StensgaardAA
import org.vorpal.research.kex.state.transformer.Token
import org.vorpal.research.kex.state.transformer.Transformer
import java.util.*

class PrimitiveDependencyAnalysis : Transformer<PrimitiveDependencyAnalysis> {
    private val isPrimitiveDependentTerm = WeakHashMap<Token, Boolean>()
    private val isPrimitiveDependentPathPredicate = mutableListOf<Boolean>()
    private val stensgaardAA = StensgaardAA()

    fun isPrimitiveDependentPathPredicate(index: Int): Boolean {
        assert(isPrimitiveDependentPathPredicate.size >= index)
        return isPrimitiveDependentPathPredicate[index]
    }

    private val Term.isPrimitiveValue: Boolean get() = this.name.contains("%primitive%")
    private val Term.getToken: Token? get() = stensgaardAA.get(this)
    private val Term.isPrimitiveDependent: Boolean
        get() {
            if (isPrimitiveDependentTerm[this.getToken] == null) {
                assert(
                    this is ConstBoolTerm ||
                            this is ConstIntTerm ||
                            this is ConstFloatTerm ||
                            this is ConstLongTerm ||
                            this is ConstCharTerm ||
                            this is ConstClassTerm ||
                            this is ConstStringTerm ||
                            this is ConstShortTerm ||
                            this is ConstByteTerm ||
                            this is ConstDoubleTerm
                )
                return false
            }
            return isPrimitiveDependentTerm[this.getToken]!!
        }

    ////////////////////////////////////////////////////////////////////
    // Term
    ////////////////////////////////////////////////////////////////////

    override fun transformArrayLoadTerm(term: ArrayLoadTerm): Term {
        stensgaardAA.transformArrayLoadTerm(term)
        assert(term.arrayRef is ArrayIndexTerm)
        isPrimitiveDependentTerm[term.getToken] =
            term.arrayRef.isPrimitiveDependent || (term.arrayRef as ArrayIndexTerm).arrayRef.isPrimitiveDependent
        return term
    }

    override fun transformArrayContainsTerm(term: ArrayContainsTerm): Term {
        stensgaardAA.transformArrayContainsTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.value.isPrimitiveDependent || term.array.isPrimitiveDependent
        return term
    }

    override fun transformArrayIndexTerm(term: ArrayIndexTerm): Term {
        stensgaardAA.transformArrayIndexTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.index.isPrimitiveDependent || term.arrayRef.isPrimitiveDependent
        return term
    }

    override fun transformArgumentTerm(term: ArgumentTerm): Term {
        error("Should not transform ArgumentTerm")
    }

    override fun transformArrayLengthTerm(term: ArrayLengthTerm): Term {
        stensgaardAA.transformArrayLengthTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformCharAtTerm(term: CharAtTerm): Term {
        stensgaardAA.transformCharAtTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.index.isPrimitiveDependent || term.string.isPrimitiveDependent
        return term
    }

    override fun transformBinaryTerm(term: BinaryTerm): Term {
        stensgaardAA.transformBinaryTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.lhv.isPrimitiveDependent || term.rhv.isPrimitiveDependent
        return term
    }

    override fun transformBoundTerm(term: BoundTerm): Term {
        stensgaardAA.transformBoundTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformCallTerm(term: CallTerm): Term {
        stensgaardAA.transformCallTerm(term)
        isPrimitiveDependentTerm[term.getToken] =
            term.arguments.fold(false) { acc, cur -> cur.isPrimitiveDependent || acc } || term.owner.isPrimitiveDependent
        return term
    }

    override fun transformCastTerm(term: CastTerm): Term {
        stensgaardAA.transformCastTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.operand.isPrimitiveDependent
        return term
    }

    override fun transformClassAccessTerm(term: ClassAccessTerm): Term {
        stensgaardAA.transformClassAccessTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.operand.isPrimitiveDependent
        return term
    }

    override fun transformCmpTerm(term: CmpTerm): Term {
        stensgaardAA.transformCmpTerm(term)
        if (term.rhv !is NullTerm) {
            isPrimitiveDependentTerm[term.getToken] = term.lhv.isPrimitiveDependent || term.rhv.isPrimitiveDependent
        } else {
            isPrimitiveDependentTerm[term.getToken] = false
        }
        return term
    }

    override fun transformConcatTerm(term: ConcatTerm): Term {
        stensgaardAA.transformConcatTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.lhv.isPrimitiveDependent || term.rhv.isPrimitiveDependent
        return term
    }

    override fun transformConstBoolTerm(term: ConstBoolTerm): Term {
        stensgaardAA.transformConstBoolTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstByteTerm(term: ConstByteTerm): Term {
        stensgaardAA.transformConstByteTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstCharTerm(term: ConstCharTerm): Term {
        stensgaardAA.transformConstCharTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstDoubleTerm(term: ConstDoubleTerm): Term {
        stensgaardAA.transformConstDoubleTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstIntTerm(term: ConstIntTerm): Term {
        stensgaardAA.transformConstIntTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstLongTerm(term: ConstLongTerm): Term {
        stensgaardAA.transformConstLongTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstFloatTerm(term: ConstFloatTerm): Term {
        stensgaardAA.transformConstFloatTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstClassTerm(term: ConstClassTerm): Term {
        stensgaardAA.transformConstClassTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstStringTerm(term: ConstStringTerm): Term {
        stensgaardAA.transformConstStringTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstShortTerm(term: ConstShortTerm): Term {
        stensgaardAA.transformConstShortTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformEndsWithTerm(term: EndsWithTerm): Term {
        stensgaardAA.transformEndsWithTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.string.isPrimitiveDependent || term.suffix.isPrimitiveDependent
        return term
    }

    override fun transformEqualsTerm(term: EqualsTerm): Term {
        stensgaardAA.transformEqualsTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.lhv.isPrimitiveDependent || term.rhv.isPrimitiveDependent
        return term
    }

    override fun transformExistsTerm(term: ExistsTerm): Term {
        stensgaardAA.transformExistsTerm(term)
        isPrimitiveDependentTerm[term.getToken] =
            term.start.isPrimitiveDependent || term.end.isPrimitiveDependent || term.body.isPrimitiveDependent
        return term
    }

    override fun transformFieldLoadTerm(term: FieldLoadTerm): Term {
        stensgaardAA.transformFieldLoadTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.field.isPrimitiveDependent
        return term
    }

    override fun transformFieldTerm(term: FieldTerm): Term {
        stensgaardAA.transformFieldTerm(term)
        return term
    }

    override fun transformForAllTerm(term: ForAllTerm): Term {
        stensgaardAA.transformForAllTerm(term)
        isPrimitiveDependentTerm[term.getToken] =
            term.start.isPrimitiveDependent || term.end.isPrimitiveDependent || term.body.isPrimitiveDependent
        return term
    }

    override fun transformIndexOfTerm(term: IndexOfTerm): Term {
        stensgaardAA.transformIndexOfTerm(term)
        isPrimitiveDependentTerm[term.getToken] =
            term.string.isPrimitiveDependent || term.substring.isPrimitiveDependent || term.offset.isPrimitiveDependent
        return term
    }

    override fun transformInstanceOfTerm(term: InstanceOfTerm): Term {
        stensgaardAA.transformInstanceOfTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformIteTerm(term: IteTerm): Term {
        stensgaardAA.transformIteTerm(term)
        isPrimitiveDependentTerm[term.getToken] =
            term.cond.isPrimitiveDependent || term.trueValue.isPrimitiveDependent || term.falseValue.isPrimitiveDependent
        return term
    }

    override fun transformLambdaTerm(term: LambdaTerm): Term {
        stensgaardAA.transformLambdaTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.parameters.fold(false) { acc, cur ->
            cur.isPrimitiveDependent || acc
        }
        return term
    }

    override fun transformNegTerm(term: NegTerm): Term {
        stensgaardAA.transformNegTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.operand.isPrimitiveDependent
        return term
    }

    override fun transformNullTerm(term: NullTerm): Term {
        stensgaardAA.transformNullTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformReturnValueTerm(term: ReturnValueTerm): Term {
        stensgaardAA.transformReturnValueTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformStartsWithTerm(term: StartsWithTerm): Term {
        stensgaardAA.transformStartsWithTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.string.isPrimitiveDependent || term.prefix.isPrimitiveDependent
        return term
    }

    override fun transformStaticClassRefTerm(term: StaticClassRefTerm): Term {
        stensgaardAA.transformStaticClassRefTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformStringContainsTerm(term: StringContainsTerm): Term {
        stensgaardAA.transformStringContainsTerm(term)
        isPrimitiveDependentTerm[term.getToken] =
            term.string.isPrimitiveDependent || term.substring.isPrimitiveDependent
        return term
    }

    override fun transformStringLengthTerm(term: StringLengthTerm): Term {
        stensgaardAA.transformStringLengthTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.string.isPrimitiveDependent
        return term
    }

    override fun transformStringParseTerm(term: StringParseTerm): Term {
        stensgaardAA.transformStringParseTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.string.isPrimitiveDependent
        return term
    }

    override fun transformSubstringTerm(term: SubstringTerm): Term {
        stensgaardAA.transformSubstringTerm(term)
        isPrimitiveDependentTerm[term.getToken] =
            term.string.isPrimitiveDependent || term.offset.isPrimitiveDependent || term.length.isPrimitiveDependent
        return term
    }

    override fun transformToStringTerm(term: ToStringTerm): Term {
        stensgaardAA.transformToStringTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.value.isPrimitiveDependent
        return term
    }

    override fun transformUndefTerm(term: UndefTerm): Term {
        stensgaardAA.transformUndefTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformValueTerm(term: ValueTerm): Term {
        stensgaardAA.transformValueTerm(term)
        if (term.isPrimitiveValue) isPrimitiveDependentTerm[term.getToken] = true
        if (isPrimitiveDependentTerm[term.getToken] == null) isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    ////////////////////////////////////////////////////////////////////
    // Predicate
    ////////////////////////////////////////////////////////////////////

    override fun transformArrayInitializerPredicate(predicate: ArrayInitializerPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += predicate.arrayRef.isPrimitiveDependent || predicate.value.isPrimitiveDependent
        } else {
            stensgaardAA.transformArrayInitializerPredicate(predicate)
            assert(predicate.arrayRef is ArrayIndexTerm)
            isPrimitiveDependentTerm[(predicate.arrayRef as ArrayIndexTerm).arrayRef.getToken] =
                predicate.value.isPrimitiveDependent
            isPrimitiveDependentTerm[predicate.arrayRef.getToken] = predicate.value.isPrimitiveDependent
        }
        return predicate
    }

    override fun transformArrayStorePredicate(predicate: ArrayStorePredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += predicate.arrayRef.isPrimitiveDependent || predicate.value.isPrimitiveDependent
        } else {
            stensgaardAA.transformArrayStorePredicate(predicate)
            assert(predicate.arrayRef is ArrayIndexTerm)
            isPrimitiveDependentTerm[(predicate.arrayRef as ArrayIndexTerm).arrayRef.getToken] =
                predicate.value.isPrimitiveDependent
            isPrimitiveDependentTerm[predicate.arrayRef.getToken] = predicate.value.isPrimitiveDependent
        }
        return predicate
    }

    override fun transformBoundStorePredicate(predicate: BoundStorePredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        } else {
            stensgaardAA.transformBoundStorePredicate(predicate)
        }
        return predicate
    }

    override fun transformCallPredicate(predicate: CallPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += (predicate.hasLhv && predicate.lhv.isPrimitiveDependent) || predicate.callTerm.isPrimitiveDependent
        } else {
            stensgaardAA.transformCallPredicate(predicate)
            if (predicate.hasLhv)
                isPrimitiveDependentTerm[predicate.lhv.getToken] = predicate.callTerm.isPrimitiveDependent
        }
        return predicate
    }

    override fun transformCatchPredicate(predicate: CatchPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        } else {
            stensgaardAA.transformCatchPredicate(predicate)
        }
        return predicate
    }

    override fun transformDefaultSwitchPredicate(predicate: DefaultSwitchPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        } else {
            stensgaardAA.transformDefaultSwitchPredicate(predicate)
        }
        return predicate
    }

    override fun transformEnterMonitorPredicate(predicate: EnterMonitorPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        } else {
            stensgaardAA.transformEnterMonitorPredicate(predicate)
        }
        return predicate
    }

    override fun transformEqualityPredicate(predicate: EqualityPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += predicate.lhv.isPrimitiveDependent || predicate.rhv.isPrimitiveDependent
        } else {
            stensgaardAA.transformEqualityPredicate(predicate)
            if (predicate.lhv !is ConstBoolTerm) {
                isPrimitiveDependentTerm[predicate.lhv.getToken] = predicate.rhv.isPrimitiveDependent
            }
        }
        return predicate
    }

    override fun transformExitMonitorPredicate(predicate: ExitMonitorPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        } else {
            stensgaardAA.transformExitMonitorPredicate(predicate)
        }
        return predicate
    }

    override fun transformFieldInitializerPredicate(predicate: FieldInitializerPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += predicate.field.isPrimitiveDependent || predicate.value.isPrimitiveDependent
        } else {
            stensgaardAA.transformFieldInitializerPredicate(predicate)
            isPrimitiveDependentTerm[predicate.field.getToken] = predicate.value.isPrimitiveDependent
        }
        return predicate
    }

    override fun transformFieldStorePredicate(predicate: FieldStorePredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += predicate.field.isPrimitiveDependent || predicate.value.isPrimitiveDependent
        } else {
            stensgaardAA.transformFieldStorePredicate(predicate)
            isPrimitiveDependentTerm[predicate.field.getToken] = predicate.value.isPrimitiveDependent
        }
        return predicate
    }

    override fun transformGenerateArrayPredicate(predicate: GenerateArrayPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += predicate.lhv.isPrimitiveDependent || predicate.length.isPrimitiveDependent || predicate.generator.isPrimitiveDependent
        } else {
            stensgaardAA.transformGenerateArrayPredicate(predicate)
            isPrimitiveDependentTerm[predicate.lhv.getToken] =
                predicate.length.isPrimitiveDependent || predicate.generator.isPrimitiveDependent
        }
        return predicate
    }

    override fun transformInequalityPredicate(predicate: InequalityPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        } else {
            stensgaardAA.transformInequalityPredicate(predicate)
        }
        return predicate
    }

    override fun transformNewArrayInitializerPredicate(predicate: NewArrayInitializerPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += predicate.lhv.isPrimitiveDependent || predicate.elements.fold(false) { acc, cur ->
                cur.isPrimitiveDependent || acc
            } || predicate.length.isPrimitiveDependent
        } else {
            stensgaardAA.transformNewArrayInitializerPredicate(predicate)
            isPrimitiveDependentTerm[predicate.lhv.getToken] = predicate.elements.fold(false) { acc, cur ->
                cur.isPrimitiveDependent || acc
            } || predicate.length.isPrimitiveDependent
        }
        return predicate
    }

    override fun transformNewArrayPredicate(predicate: NewArrayPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += predicate.lhv.isPrimitiveDependent || predicate.dimensions.fold(false) { acc, cur ->
                cur.isPrimitiveDependent || acc
            }
        } else {
            stensgaardAA.transformNewArrayPredicate(predicate)
            isPrimitiveDependentTerm[predicate.lhv.getToken] = predicate.dimensions.fold(false) { acc, cur ->
                cur.isPrimitiveDependent || acc
            }
        }
        return predicate
    }

    override fun transformNewInitializerPredicate(predicate: NewInitializerPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        } else {
            stensgaardAA.transformNewInitializerPredicate(predicate)
        }
        return predicate
    }

    override fun transformNewPredicate(predicate: NewPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        } else {
            stensgaardAA.transformNewPredicate(predicate)
        }
        return predicate
    }

    override fun transformThrowPredicate(predicate: ThrowPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        } else {
            stensgaardAA.transformThrowPredicate(predicate)
        }
        return predicate
    }
}