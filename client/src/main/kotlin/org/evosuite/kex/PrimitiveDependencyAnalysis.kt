package org.evosuite.kex

import org.vorpal.research.kex.state.predicate.*
import org.vorpal.research.kex.state.term.*
import org.vorpal.research.kex.state.transformer.Token
import org.vorpal.research.kex.state.transformer.Transformer
import java.util.*

class PrimitiveDependencyAnalysis : Transformer<PrimitiveDependencyAnalysis> {
    private val isPrimitiveDependentTerm = WeakHashMap<Term, Boolean>()
    private val isPrimitiveDependentPathPredicate = mutableListOf<Boolean>()
    // private val mustAliasAnalysis = MustAliasAnalysis()

    fun isPrimitiveDependentPathPredicate(index: Int): Boolean {
        assert(isPrimitiveDependentPathPredicate.size >= index)
        return isPrimitiveDependentPathPredicate[index]
    }

    private val Term.isPrimitiveValue: Boolean get() = this.name.contains("%primitive%")
    // private val Term.getToken: Token? get() = mustAliasAnalysis.get(this)
    private val Term.getToken: Term get() = this
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
        //mustAliasAnalysis.transformArrayLoadTerm(term)
        assert(term.arrayRef is ArrayIndexTerm)
        isPrimitiveDependentTerm[term.getToken] =
            term.arrayRef.isPrimitiveDependent || (term.arrayRef as ArrayIndexTerm).arrayRef.isPrimitiveDependent
        return term
    }

    override fun transformArrayContainsTerm(term: ArrayContainsTerm): Term {
        //mustAliasAnalysis.transformArrayContainsTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.value.isPrimitiveDependent || term.array.isPrimitiveDependent
        return term
    }

    override fun transformArrayIndexTerm(term: ArrayIndexTerm): Term {
        //mustAliasAnalysis.transformArrayIndexTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.index.isPrimitiveDependent || term.arrayRef.isPrimitiveDependent
        return term
    }

    override fun transformArgumentTerm(term: ArgumentTerm): Term {
        error("Should not transform ArgumentTerm")
    }

    override fun transformArrayLengthTerm(term: ArrayLengthTerm): Term {
        //mustAliasAnalysis.transformArrayLengthTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformCharAtTerm(term: CharAtTerm): Term {
        //mustAliasAnalysis.transformCharAtTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.index.isPrimitiveDependent || term.string.isPrimitiveDependent
        return term
    }

    override fun transformBinaryTerm(term: BinaryTerm): Term {
        //mustAliasAnalysis.transformBinaryTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.lhv.isPrimitiveDependent || term.rhv.isPrimitiveDependent
        return term
    }

    override fun transformBoundTerm(term: BoundTerm): Term {
        //mustAliasAnalysis.transformBoundTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformCallTerm(term: CallTerm): Term {
        //mustAliasAnalysis.transformCallTerm(term)
        isPrimitiveDependentTerm[term.getToken] =
            term.arguments.fold(false) { acc, cur -> cur.isPrimitiveDependent || acc } || term.owner.isPrimitiveDependent
        return term
    }

    override fun transformCastTerm(term: CastTerm): Term {
        //mustAliasAnalysis.transformCastTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.operand.isPrimitiveDependent
        return term
    }

    override fun transformClassAccessTerm(term: ClassAccessTerm): Term {
        //mustAliasAnalysis.transformClassAccessTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.operand.isPrimitiveDependent
        return term
    }

    override fun transformCmpTerm(term: CmpTerm): Term {
        //mustAliasAnalysis.transformCmpTerm(term)
        if (term.rhv !is NullTerm) {
            isPrimitiveDependentTerm[term.getToken] = term.lhv.isPrimitiveDependent || term.rhv.isPrimitiveDependent
        } else {
            isPrimitiveDependentTerm[term.getToken] = false
        }
        return term
    }

    override fun transformConcatTerm(term: ConcatTerm): Term {
        //mustAliasAnalysis.transformConcatTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.lhv.isPrimitiveDependent || term.rhv.isPrimitiveDependent
        return term
    }

    override fun transformConstBoolTerm(term: ConstBoolTerm): Term {
        //mustAliasAnalysis.transformConstBoolTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstByteTerm(term: ConstByteTerm): Term {
        //mustAliasAnalysis.transformConstByteTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstCharTerm(term: ConstCharTerm): Term {
        //mustAliasAnalysis.transformConstCharTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstDoubleTerm(term: ConstDoubleTerm): Term {
        //mustAliasAnalysis.transformConstDoubleTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstIntTerm(term: ConstIntTerm): Term {
        //mustAliasAnalysis.transformConstIntTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstLongTerm(term: ConstLongTerm): Term {
        //mustAliasAnalysis.transformConstLongTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstFloatTerm(term: ConstFloatTerm): Term {
        //mustAliasAnalysis.transformConstFloatTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstClassTerm(term: ConstClassTerm): Term {
        //mustAliasAnalysis.transformConstClassTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstStringTerm(term: ConstStringTerm): Term {
        //mustAliasAnalysis.transformConstStringTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformConstShortTerm(term: ConstShortTerm): Term {
        //mustAliasAnalysis.transformConstShortTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformEndsWithTerm(term: EndsWithTerm): Term {
        //mustAliasAnalysis.transformEndsWithTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.string.isPrimitiveDependent || term.suffix.isPrimitiveDependent
        return term
    }

    override fun transformEqualsTerm(term: EqualsTerm): Term {
        //mustAliasAnalysis.transformEqualsTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.lhv.isPrimitiveDependent || term.rhv.isPrimitiveDependent
        return term
    }

    override fun transformExistsTerm(term: ExistsTerm): Term {
        //mustAliasAnalysis.transformExistsTerm(term)
        isPrimitiveDependentTerm[term.getToken] =
            term.start.isPrimitiveDependent || term.end.isPrimitiveDependent || term.body.isPrimitiveDependent
        return term
    }

    override fun transformFieldLoadTerm(term: FieldLoadTerm): Term {
        //mustAliasAnalysis.transformFieldLoadTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.field.isPrimitiveDependent
        return term
    }

    override fun transformFieldTerm(term: FieldTerm): Term {
        //mustAliasAnalysis.transformFieldTerm(term)
        return term
    }

    override fun transformForAllTerm(term: ForAllTerm): Term {
        //mustAliasAnalysis.transformForAllTerm(term)
        isPrimitiveDependentTerm[term.getToken] =
            term.start.isPrimitiveDependent || term.end.isPrimitiveDependent || term.body.isPrimitiveDependent
        return term
    }

    override fun transformIndexOfTerm(term: IndexOfTerm): Term {
        //mustAliasAnalysis.transformIndexOfTerm(term)
        isPrimitiveDependentTerm[term.getToken] =
            term.string.isPrimitiveDependent || term.substring.isPrimitiveDependent || term.offset.isPrimitiveDependent
        return term
    }

    override fun transformInstanceOfTerm(term: InstanceOfTerm): Term {
        //mustAliasAnalysis.transformInstanceOfTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformIteTerm(term: IteTerm): Term {
        //mustAliasAnalysis.transformIteTerm(term)
        isPrimitiveDependentTerm[term.getToken] =
            term.cond.isPrimitiveDependent || term.trueValue.isPrimitiveDependent || term.falseValue.isPrimitiveDependent
        return term
    }

    override fun transformLambdaTerm(term: LambdaTerm): Term {
        //mustAliasAnalysis.transformLambdaTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.parameters.fold(false) { acc, cur ->
            cur.isPrimitiveDependent || acc
        }
        return term
    }

    override fun transformNegTerm(term: NegTerm): Term {
        //mustAliasAnalysis.transformNegTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.operand.isPrimitiveDependent
        return term
    }

    override fun transformNullTerm(term: NullTerm): Term {
        //mustAliasAnalysis.transformNullTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformReturnValueTerm(term: ReturnValueTerm): Term {
        //mustAliasAnalysis.transformReturnValueTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformStartsWithTerm(term: StartsWithTerm): Term {
        //mustAliasAnalysis.transformStartsWithTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.string.isPrimitiveDependent || term.prefix.isPrimitiveDependent
        return term
    }

    override fun transformStaticClassRefTerm(term: StaticClassRefTerm): Term {
        //mustAliasAnalysis.transformStaticClassRefTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformStringContainsTerm(term: StringContainsTerm): Term {
        //mustAliasAnalysis.transformStringContainsTerm(term)
        isPrimitiveDependentTerm[term.getToken] =
            term.string.isPrimitiveDependent || term.substring.isPrimitiveDependent
        return term
    }

    override fun transformStringLengthTerm(term: StringLengthTerm): Term {
        //mustAliasAnalysis.transformStringLengthTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.string.isPrimitiveDependent
        return term
    }

    override fun transformStringParseTerm(term: StringParseTerm): Term {
        //mustAliasAnalysis.transformStringParseTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.string.isPrimitiveDependent
        return term
    }

    override fun transformSubstringTerm(term: SubstringTerm): Term {
        //mustAliasAnalysis.transformSubstringTerm(term)
        isPrimitiveDependentTerm[term.getToken] =
            term.string.isPrimitiveDependent || term.offset.isPrimitiveDependent || term.length.isPrimitiveDependent
        return term
    }

    override fun transformToStringTerm(term: ToStringTerm): Term {
        //mustAliasAnalysis.transformToStringTerm(term)
        isPrimitiveDependentTerm[term.getToken] = term.value.isPrimitiveDependent
        return term
    }

    override fun transformUndefTerm(term: UndefTerm): Term {
        //mustAliasAnalysis.transformUndefTerm(term)
        isPrimitiveDependentTerm[term.getToken] = false
        return term
    }

    override fun transformValueTerm(term: ValueTerm): Term {
        //mustAliasAnalysis.transformValueTerm(term)
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
            //mustAliasAnalysis.transformArrayInitializerPredicate(predicate)
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
            //mustAliasAnalysis.transformArrayStorePredicate(predicate)
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
            //mustAliasAnalysis.transformBoundStorePredicate(predicate)
        }
        return predicate
    }

    override fun transformCallPredicate(predicate: CallPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += (predicate.hasLhv && predicate.lhv.isPrimitiveDependent) || predicate.callTerm.isPrimitiveDependent
        } else {
            //mustAliasAnalysis.transformCallPredicate(predicate)
            if (predicate.hasLhv)
                isPrimitiveDependentTerm[predicate.lhv.getToken] = predicate.callTerm.isPrimitiveDependent
        }
        return predicate
    }

    override fun transformCatchPredicate(predicate: CatchPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        } else {
            //mustAliasAnalysis.transformCatchPredicate(predicate)
        }
        return predicate
    }

    override fun transformDefaultSwitchPredicate(predicate: DefaultSwitchPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        } else {
            //mustAliasAnalysis.transformDefaultSwitchPredicate(predicate)
        }
        return predicate
    }

    override fun transformEnterMonitorPredicate(predicate: EnterMonitorPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        } else {
            //mustAliasAnalysis.transformEnterMonitorPredicate(predicate)
        }
        return predicate
    }

    override fun transformEqualityPredicate(predicate: EqualityPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += predicate.lhv.isPrimitiveDependent || predicate.rhv.isPrimitiveDependent
        } else {
            //mustAliasAnalysis.transformEqualityPredicate(predicate)
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
            //mustAliasAnalysis.transformExitMonitorPredicate(predicate)
        }
        return predicate
    }

    override fun transformFieldInitializerPredicate(predicate: FieldInitializerPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += predicate.field.isPrimitiveDependent || predicate.value.isPrimitiveDependent
        } else {
            //mustAliasAnalysis.transformFieldInitializerPredicate(predicate)
            isPrimitiveDependentTerm[predicate.field.getToken] = predicate.value.isPrimitiveDependent
        }
        return predicate
    }

    override fun transformFieldStorePredicate(predicate: FieldStorePredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += predicate.field.isPrimitiveDependent || predicate.value.isPrimitiveDependent
        } else {
            //mustAliasAnalysis.transformFieldStorePredicate(predicate)
            isPrimitiveDependentTerm[predicate.field.getToken] = predicate.value.isPrimitiveDependent
        }
        return predicate
    }

    override fun transformGenerateArrayPredicate(predicate: GenerateArrayPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += predicate.lhv.isPrimitiveDependent || predicate.length.isPrimitiveDependent || predicate.generator.isPrimitiveDependent
        } else {
            //mustAliasAnalysis.transformGenerateArrayPredicate(predicate)
            isPrimitiveDependentTerm[predicate.lhv.getToken] =
                predicate.length.isPrimitiveDependent || predicate.generator.isPrimitiveDependent
        }
        return predicate
    }

    override fun transformInequalityPredicate(predicate: InequalityPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        } else {
            //mustAliasAnalysis.transformInequalityPredicate(predicate)
        }
        return predicate
    }

    override fun transformNewArrayInitializerPredicate(predicate: NewArrayInitializerPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += predicate.lhv.isPrimitiveDependent || predicate.elements.fold(false) { acc, cur ->
                cur.isPrimitiveDependent || acc
            } || predicate.length.isPrimitiveDependent
        } else {
            //mustAliasAnalysis.transformNewArrayInitializerPredicate(predicate)
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
            //mustAliasAnalysis.transformNewArrayPredicate(predicate)
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
            //mustAliasAnalysis.transformNewInitializerPredicate(predicate)
        }
        return predicate
    }

    override fun transformNewPredicate(predicate: NewPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        } else {
            //mustAliasAnalysis.transformNewPredicate(predicate)
        }
        return predicate
    }

    override fun transformThrowPredicate(predicate: ThrowPredicate): Predicate {
        if (predicate.type == PredicateType.Path()) {
            isPrimitiveDependentPathPredicate += false
        } else {
            //mustAliasAnalysis.transformThrowPredicate(predicate)
        }
        return predicate
    }
}