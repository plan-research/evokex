package org.evosuite.kex

import org.vorpal.research.kex.ktype.KexPointer
import org.vorpal.research.kex.state.predicate.*
import org.vorpal.research.kex.state.term.*
import org.vorpal.research.kex.state.transformer.Token
import org.vorpal.research.kex.state.transformer.Transformer
import org.vorpal.research.kthelper.collection.DisjointSet

class MustAliasAnalysis : Transformer<MustAliasAnalysis> {
    private val relations = DisjointSet<Term>()
    private val root = hashMapOf<Term, Token?>()

    private fun emplace(term: Term) {
        if (term !in root) root[term] = relations.emplace(term)
    }

    private fun join(term1: Term, term2: Term) {
        relations.join(root[term1]!!, root[term2]!!)
        root[term1] = root[term1]!!.getRoot()
        root[term2] = root[term2]!!.getRoot()
    }

    fun get(term: Term) = root[term]

    ////////////////////////////////////////////////////////////////////
    // Term
    ////////////////////////////////////////////////////////////////////

    override fun transformArrayLoadTerm(term: ArrayLoadTerm): Term {
        emplace(term)
        if (term.type is KexPointer) {
            join(term, term.arrayRef)
            join(term, (term.arrayRef as ArrayIndexTerm).arrayRef)
        }
        join(term.arrayRef, (term.arrayRef as ArrayIndexTerm).arrayRef)
        return term
    }

    override fun transformArrayContainsTerm(term: ArrayContainsTerm): Term {
        emplace(term)
        return term
    }

    override fun transformArrayIndexTerm(term: ArrayIndexTerm): Term {
        emplace(term)
        join(term, term.arrayRef)
        return term
    }

    override fun transformArgumentTerm(term: ArgumentTerm): Term {
        error("Should not transform ArgumentTerm")
    }

    override fun transformArrayLengthTerm(term: ArrayLengthTerm): Term {
        emplace(term)
        return term
    }

    override fun transformCharAtTerm(term: CharAtTerm): Term {
        emplace(term)
        return term
    }

    override fun transformBinaryTerm(term: BinaryTerm): Term {
        emplace(term)
        return term
    }

    override fun transformBoundTerm(term: BoundTerm): Term {
        emplace(term)
        return term
    }

    override fun transformCallTerm(term: CallTerm): Term {
        emplace(term)
        return term
    }

    override fun transformCastTerm(term: CastTerm): Term {
        emplace(term)
        if(term.type is KexPointer && term.operand.type is KexPointer) {
            join(term, term.operand)
        }
        return term
    }

    override fun transformClassAccessTerm(term: ClassAccessTerm): Term {
        emplace(term)
        return term
    }

    override fun transformCmpTerm(term: CmpTerm): Term {
        emplace(term)
        return term
    }

    override fun transformConcatTerm(term: ConcatTerm): Term {
        emplace(term)
        return term
    }

    override fun transformConstBoolTerm(term: ConstBoolTerm): Term {
        emplace(term)
        return term
    }

    override fun transformConstByteTerm(term: ConstByteTerm): Term {
        emplace(term)
        return term
    }

    override fun transformConstCharTerm(term: ConstCharTerm): Term {
        emplace(term)
        return term
    }

    override fun transformConstDoubleTerm(term: ConstDoubleTerm): Term {
        emplace(term)
        return term
    }

    override fun transformConstIntTerm(term: ConstIntTerm): Term {
        emplace(term)
        return term
    }

    override fun transformConstLongTerm(term: ConstLongTerm): Term {
        emplace(term)
        return term
    }

    override fun transformConstFloatTerm(term: ConstFloatTerm): Term {
        emplace(term)
        return term
    }

    override fun transformConstClassTerm(term: ConstClassTerm): Term {
        emplace(term)
        return term
    }

    override fun transformConstStringTerm(term: ConstStringTerm): Term {
        emplace(term)
        return term
    }

    override fun transformConstShortTerm(term: ConstShortTerm): Term {
        emplace(term)
        return term
    }

    override fun transformEndsWithTerm(term: EndsWithTerm): Term {
        emplace(term)
        return term
    }

    override fun transformEqualsTerm(term: EqualsTerm): Term {
        emplace(term)
        if(term.lhv.type is KexPointer && term.rhv.type is KexPointer) {
            join(term.lhv, term.rhv)
        }
        return term
    }

    override fun transformExistsTerm(term: ExistsTerm): Term {
        emplace(term)
        return term
    }

    override fun transformFieldLoadTerm(term: FieldLoadTerm): Term {
        emplace(term)
        if(term.type is KexPointer && term.field.type is KexPointer) {
            join(term, term.field)
        }
        return term
    }

    override fun transformFieldTerm(term: FieldTerm): Term {
        emplace(term)
        return term
    }

    override fun transformForAllTerm(term: ForAllTerm): Term {
        emplace(term)
        return term
    }

    override fun transformIndexOfTerm(term: IndexOfTerm): Term {
        emplace(term)
        return term
    }

    override fun transformInstanceOfTerm(term: InstanceOfTerm): Term {
        emplace(term)
        return term
    }

    override fun transformIteTerm(term: IteTerm): Term {
        emplace(term)
        return term
    }

    override fun transformLambdaTerm(term: LambdaTerm): Term {
        emplace(term)
        return term
    }

    override fun transformNegTerm(term: NegTerm): Term {
        emplace(term)
        return term
    }

    override fun transformNullTerm(term: NullTerm): Term {
        emplace(term)
        return term
    }

    override fun transformReturnValueTerm(term: ReturnValueTerm): Term {
        emplace(term)
        return term
    }

    override fun transformStartsWithTerm(term: StartsWithTerm): Term {
        emplace(term)
        return term
    }

    override fun transformStaticClassRefTerm(term: StaticClassRefTerm): Term {
        emplace(term)
        return term
    }

    override fun transformStringContainsTerm(term: StringContainsTerm): Term {
        emplace(term)
        return term
    }

    override fun transformStringLengthTerm(term: StringLengthTerm): Term {
        emplace(term)
        return term
    }

    override fun transformStringParseTerm(term: StringParseTerm): Term {
        emplace(term)
        return term
    }

    override fun transformSubstringTerm(term: SubstringTerm): Term {
        emplace(term)
        return term
    }

    override fun transformToStringTerm(term: ToStringTerm): Term {
        emplace(term)
        return term
    }

    override fun transformUndefTerm(term: UndefTerm): Term {
        emplace(term)
        return term
    }

    override fun transformValueTerm(term: ValueTerm): Term {
        emplace(term)
        return term
    }

    ////////////////////////////////////////////////////////////////////
    // Predicate
    ////////////////////////////////////////////////////////////////////

    override fun transformArrayInitializerPredicate(predicate: ArrayInitializerPredicate): Predicate {
        if (predicate.type == PredicateType.State() && predicate.arrayRef.type is KexPointer && predicate.value.type is KexPointer) {
            join(predicate.arrayRef, predicate.value)
        }
        join(predicate.arrayRef, (predicate.arrayRef as ArrayIndexTerm).arrayRef)
        return predicate
    }

    override fun transformArrayStorePredicate(predicate: ArrayStorePredicate): Predicate {
        if (predicate.type == PredicateType.State() && predicate.arrayRef.type is KexPointer && predicate.value.type is KexPointer) {
            join(predicate.arrayRef, predicate.value)
        }
        join(predicate.arrayRef, (predicate.arrayRef as ArrayIndexTerm).arrayRef)
        return predicate
    }

    override fun transformBoundStorePredicate(predicate: BoundStorePredicate): Predicate {
        return predicate
    }

    override fun transformCallPredicate(predicate: CallPredicate): Predicate {
        if (predicate.type == PredicateType.State() && predicate.hasLhv && predicate.lhv.type is KexPointer) {
            join(predicate.lhv, predicate.call)
        }
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
        if (predicate.type == PredicateType.State() && predicate.lhv.type is KexPointer && predicate.rhv.type is KexPointer) {
            join(predicate.lhv, predicate.rhv)
        }
        return predicate
    }

    override fun transformExitMonitorPredicate(predicate: ExitMonitorPredicate): Predicate {
        return predicate
    }

    override fun transformFieldInitializerPredicate(predicate: FieldInitializerPredicate): Predicate {
        if (predicate.type == PredicateType.State() && predicate.field.type is KexPointer && predicate.value.type is KexPointer) {
            join(predicate.field, predicate.value)
        }
        return predicate
    }

    override fun transformFieldStorePredicate(predicate: FieldStorePredicate): Predicate {
        if (predicate.type == PredicateType.State() && predicate.field.type is KexPointer && predicate.value.type is KexPointer) {
            join(predicate.field, predicate.value)
        }
        return predicate
    }

    override fun transformGenerateArrayPredicate(predicate: GenerateArrayPredicate): Predicate {
        if (predicate.type == PredicateType.State()) {
            emplace(predicate.lhv)
        }
        return predicate
    }

    override fun transformInequalityPredicate(predicate: InequalityPredicate): Predicate {
        return predicate
    }

    override fun transformNewArrayInitializerPredicate(predicate: NewArrayInitializerPredicate): Predicate {
        if (predicate.type == PredicateType.State()) {
            emplace(predicate.lhv)
            for (el in predicate.elements) {
                join(predicate.lhv, el)
            }
        }
        return predicate
    }

    override fun transformNewArrayPredicate(predicate: NewArrayPredicate): Predicate {
        if (predicate.type == PredicateType.State()) {
            emplace(predicate.lhv)
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