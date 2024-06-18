package org.evosuite.kex

import kotlinx.coroutines.DelicateCoroutinesApi
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.InternalSerializationApi
import org.evosuite.TestGenerationContext
import org.evosuite.testcase.TestCase
import org.evosuite.testcase.statements.*
import org.evosuite.testcase.variable.*
import org.evosuite.utils.generic.*
import org.vorpal.research.kex.parameters.Parameters
import org.vorpal.research.kex.reanimator.actionsequence.*
import org.vorpal.research.kex.util.getConstructor
import org.vorpal.research.kex.util.getMethod
import org.vorpal.research.kex.util.loadClass
import org.vorpal.research.kfg.ir.Field
import org.vorpal.research.kfg.ir.Method
import org.vorpal.research.kfg.type.ArrayType
import org.vorpal.research.kthelper.assert.unreachable
import java.lang.reflect.Array
import java.lang.reflect.Type
import kotlin.time.ExperimentalTime

private typealias KFGType = org.vorpal.research.kfg.type.Type
private typealias KFGClass = org.vorpal.research.kfg.ir.Class

@ExperimentalTime
@InternalSerializationApi
@ExperimentalSerializationApi
@DelicateCoroutinesApi
class ActionSequence2EvosuiteStatements(private val testCase: TestCase) {

    private val reflectionUtils get() = KexService.reflectionUtils
    private val loader get() = TestGenerationContext.getInstance().classLoaderForSUT

    private val refs = mutableMapOf<String, VariableReference>()

    private val ActionSequence.ref: VariableReference get() = refs[name]!!

    private operator fun Statement.unaryPlus() {
        testCase.addStatement(this)
    }

    private fun ActionSequence.createRef(type: Type): VariableReference = VariableReferenceImpl(testCase, type).also {
        refs[name] = it
    }

    private val ActionSequence.asInt: Int get() = (this as PrimaryValue<*>).value as Int
    private val Class<*>.sutClass: Class<*> get() = loader.loadClass(name)
    private val String.asConstantValue
        get() = ConstantValue(testCase, GenericClass(String::class.java), this)
    private val Class<*>.asConstantValue
        get() = ConstantValue(testCase, GenericClass(Class::class.java), this)

    private val KFGType.java: Type
        get() = when {
            isVoid -> Void.TYPE
            this is ArrayType -> GenericArrayTypeImpl.createArrayType(component.java)
            else -> loader.loadClass(this)
        }

    private val KFGClass.java: Class<*> get() = loader.loadClass(this)

    fun generateStatements(actionSequence: ActionSequence) {
        if (actionSequence.name in refs) return
        when (actionSequence) {
            is ActionList -> actionSequence.list.forEach { generateStatementsFromAction(actionSequence, it) }
            is ReflectionList -> actionSequence.list.forEach { generateStatementsFromReflection(actionSequence, it) }
            is TestCall -> generateTestCall(actionSequence)
            is UnknownSequence, is MockList -> unreachable("not supported lol")
            is PrimaryValue<*>, is StringValue -> {
                // nothing to generate
            }
        }
    }

    fun generateTestCall(method: Method, parameters: Parameters<ActionSequence>) {
        generateCall(method, parameters.instance, parameters.arguments)
    }

    private fun ActionSequence.generateAndGetRef(): VariableReference = when (this) {
        is PrimaryValue<*> -> if (value == null) { // evosuite lol (issue with getStPosition for NullStatement)
            if (name in refs) {
                ref
            } else {
                NullStatement(testCase, Object::class.java.sutClass).let {
                    +it
                    refs[name] = it.returnValue
                    it.returnValue
                }
            }
        } else {
            ConstantValue(testCase, GenericClass(value!!.javaClass), value).apply {
                changeClassLoader(loader)
            }
        }

        is StringValue -> value.asConstantValue
        else -> {
            generateStatements(this)
            ref
        }
    }

    private fun generateTestCall(testCall: TestCall) {
        generateCall(testCall.test, testCall.instance, testCall.args)
    }

    private fun generateStatementsFromReflection(owner: ReflectionList, call: ReflectionCall) {
        when (call) {
            is ReflectionArrayWrite -> generateReflectionCall(owner, call)
            is ReflectionNewArray -> generateReflectionCall(owner, call)
            is ReflectionNewInstance -> generateReflectionCall(owner, call)
            is ReflectionSetField -> generateReflectionCall(owner, call)
            is ReflectionSetStaticField -> generateReflectionCall(call)
            is ReflectionGetField -> generateReflectionCall(owner, call)
            is ReflectionGetStaticField -> generateReflectionCall(owner, call)
        }
    }

    private fun generateReflectionCall(owner: ReflectionList, call: ReflectionGetStaticField) {
        generateReflectionGetField(owner, null, call.field)
    }

    private fun generateReflectionCall(owner: ReflectionList, call: ReflectionGetField) {
        generateReflectionGetField(owner, call.owner, call.field)
    }

    private fun generateReflectionGetField(owner: ReflectionList, callOwner: ActionSequence?, field: Field) {
        val type = field.type.java
        val callOwnerRef = callOwner?.ref ?: PrimaryValue(null).generateAndGetRef()
        val method = reflectionUtils.getPrimitiveFieldMap[type.typeName] ?: reflectionUtils.getField
        val klass = field.klass.java.asConstantValue
        val name = field.name.asConstantValue
        val args = listOf(callOwnerRef, klass, name)
        val ref = owner.createRef(type)
        +KexReflectionStatement(testCase, method.name, args, ref)
    }

    private fun generateReflectionCall(owner: ReflectionList, call: ReflectionArrayWrite) {
        val ownerRef = owner.ref
        val index = call.index.generateAndGetRef()
        val value = call.value.generateAndGetRef()
        val args = listOf(ownerRef, index, value)
        val method = reflectionUtils.setPrimitiveElementMap[value.type.typeName] ?: reflectionUtils.setElement
        +KexReflectionStatement(testCase, method.name, args)
    }

    private fun generateReflectionCall(owner: ReflectionList, call: ReflectionNewArray) {
        val type = call.type.java
        val elementType = call.asArray.component.java
        val length = call.length.generateAndGetRef()
        val primitiveMethod = reflectionUtils.newPrimitiveArrayMap[elementType.typeName]
        val args: List<VariableReference>
        val method = if (primitiveMethod != null) {
            args = listOf(length)
            primitiveMethod
        } else {
            args = listOf(elementType.typeName.asConstantValue, length)
            reflectionUtils.newArray
        }
        val ref = owner.createRef(type)
        +KexReflectionStatement(testCase, method.name, args, ref)
    }

    private fun generateReflectionCall(owner: ReflectionList, call: ReflectionNewInstance) {
        val type = call.type.java
        val method = reflectionUtils.newInstance
        val args = listOf(type.typeName.asConstantValue)
        val ref = owner.createRef(type)
        +KexReflectionStatement(testCase, method.name, args, ref)
    }

    private fun generateReflectionSetField(owner: ActionSequence?, field: Field, value: ActionSequence) {
        val ownerRef = owner?.ref ?: PrimaryValue(null).generateAndGetRef()
        val valueRef = value.generateAndGetRef()
        val method = reflectionUtils.setPrimitiveFieldMap[valueRef.type.typeName] ?: reflectionUtils.setField
        val klass = field.klass.java.asConstantValue
        val name = field.name.asConstantValue
        val args = listOf(ownerRef, klass, name, valueRef)
        +KexReflectionStatement(testCase, method.name, args)
    }


    private fun generateReflectionCall(owner: ReflectionList, call: ReflectionSetField) {
        generateReflectionSetField(owner, call.field, call.value)
    }

    private fun generateReflectionCall(call: ReflectionSetStaticField) {
        generateReflectionSetField(null, call.field, call.value)
    }

    private fun generateStatementsFromAction(owner: ActionList, action: CodeAction) {
        when (action) {
            is ArrayWrite -> generateAction(owner, action)
            is ConstructorCall -> generateAction(owner, action)
            is DefaultConstructorCall -> generateAction(owner, action)
            is EnumValueCreation -> generateAction(owner, action)
            is ExternalConstructorCall -> generateAction(owner, action)
            is ExternalMethodCall -> generateAction(owner, action)
            is FieldSetter -> generateAction(owner, action)
            is InnerClassConstructorCall -> generateAction(owner, action)
            is MethodCall -> generateAction(owner, action)
            is NewArray -> generateAction(owner, action)
            is NewArrayWithInitializer -> generateAction(owner, action)
            is StaticFieldGetter -> generateAction(owner, action)
            is StaticFieldSetter -> generateAction(action)
            is StaticMethodCall -> generateAction(action)
            is ArrayClassConstantGetter -> generateAction(owner, action)
            is ClassConstantGetter -> generateAction(owner, action)
        }
    }

    private fun generateAction(owner: ActionSequence, actionSequence: ClassConstantGetter) {
        val ref = owner.createRef(Class::class.java.sutClass)
        val value = ClassPrimitiveStatement(testCase, actionSequence.type.java as Class<*>)
        value.setRetval(ref)
        +value
    }

    private fun generateAction(owner: ActionSequence, action: ArrayClassConstantGetter) {
        val clazz = action.elementType.generateAndGetRef()

        val newInstanceMethod = GenericMethod(
            Array::class.java.getMethod(
                loader, "newInstance",
                "Ljava/lang/Class;I"
            ), Array::class.java.sutClass
        )
        val array = MethodStatement(
            testCase, newInstanceMethod, null,
            mutableListOf(clazz, ConstantValue(testCase, GenericClass(Int::class.java), 0))
        )
        +array

        val ref = owner.createRef(Class::class.java.sutClass)
        val getClass = MethodStatement(
            testCase,
            GenericMethod(
                Object::class.java.getMethod(loader, "getClass"),
                Object::class.java.sutClass
            ),
            array.returnValue, mutableListOf(), ref
        )
        +getClass
    }

    private fun generateAction(owner: ActionList, action: ArrayWrite) {
        val value = action.value.generateAndGetRef()
        val index = ArrayIndex(
            testCase, owner.ref as ArrayReference,
            action.index.asInt
        )
        +AssignmentStatement(testCase, index, value)
    }

    private fun generateAction(owner: ActionList, action: ConstructorCall) {
        generateCall(action.constructor, null, action.args, owner)
    }

    private fun generateAction(owner: ActionList, action: DefaultConstructorCall) {
        val type = action.klass.java
        val constructor = type.getConstructor()
        val ref = owner.createRef(type)
        +ConstructorStatement(testCase, GenericConstructor(constructor, type), ref, emptyList())
    }

    private fun generateAction(owner: ActionList, action: EnumValueCreation) {
        val type = action.klass.java
        val statement = PrimitiveStatement.getPrimitiveStatement(testCase, type)
        statement.value = type.enumConstants.find { (it as Enum<*>).name == action.name }
        refs[owner.name] = statement.returnValue
        +statement
    }

    private fun generateAction(owner: ActionList, action: ExternalConstructorCall) {
        generateCall(action.constructor, null, action.args, owner)
    }

    private fun generateAction(owner: ActionList, action: ExternalMethodCall) {
        generateCall(action.method, action.instance, action.args, owner)
    }

    private fun generateAction(owner: ActionList, action: FieldSetter) {
        val value = action.value.generateAndGetRef()
        val fieldOwner = action.field.klass.java
        val fieldRef = FieldReference(
            testCase, GenericField(fieldOwner.getField(action.field.name), fieldOwner), owner.ref
        )
        +AssignmentStatement(testCase, fieldRef, value)
    }

    private fun generateAction(owner: ActionList, action: InnerClassConstructorCall) {
        TODO("it seems like problems in evosuite api")
    }

    private fun generateAction(owner: ActionList, action: MethodCall) {
        generateCall(action.method, owner, action.args)
    }

    private fun generateNewArray(owner: ActionSequence, type: Type, length: Int): ArrayReference {
        val arrayReference = ArrayReference(testCase, GenericClass(type), length)
        refs[owner.name] = arrayReference
        +ArrayStatement(testCase, arrayReference, intArrayOf(length))
        return arrayReference
    }

    private fun generateAction(owner: ActionList, action: NewArray) {
        val type = action.klass.java
        val length = action.length.asInt
        generateNewArray(owner, type, length)
    }

    private fun generateAction(owner: ActionList, action: NewArrayWithInitializer) {
        val type = action.klass.java
        val length = action.elements.size
        val array = generateNewArray(owner, type, length)
        action.elements.forEachIndexed { index, value ->
            val valueRef = value.generateAndGetRef()
            val indexRef = ArrayIndex(testCase, array, index)
            +AssignmentStatement(testCase, indexRef, valueRef)
        }
    }

    private fun generateAction(owner: ActionList, action: StaticFieldGetter) {
        val fieldOwner = action.field.klass.java
        val field = GenericField(fieldOwner.getField(action.field.name), fieldOwner)
        val ref = owner.createRef(action.field.type.java)
        +FieldStatement(testCase, field, null, ref)
    }

    private fun generateAction(action: StaticFieldSetter) {
        val value = action.value.generateAndGetRef()
        val fieldOwner = action.field.klass.java
        val field = GenericField(fieldOwner.getField(action.field.name), fieldOwner)
        val fieldRef = FieldReference(testCase, field)
        +AssignmentStatement(testCase, fieldRef, value)
    }

    private fun generateAction(action: StaticMethodCall) {
        generateCall(action.method, null, action.args)
    }

    private fun generateCall(
        method: Method,
        callee: ActionSequence?,
        args: List<ActionSequence>,
        ret: ActionSequence? = null
    ) {
        val type = method.klass.java
        val calleeRef = callee?.generateAndGetRef()
        val argsRef = args.map { it.generateAndGetRef() }
        val retRef = ret?.createRef(method.returnType.java)
        if (method.isConstructor) {
            val genericConstructor = GenericConstructor(type.getConstructor(method, loader), type)
            if (retRef != null) {
                +ConstructorStatement(testCase, genericConstructor, retRef, argsRef)
            } else {
                +ConstructorStatement(testCase, genericConstructor, argsRef)
            }
        } else {
            val genericMethod = GenericMethod(type.getMethod(method, loader), type)
            if (retRef != null) {
                +MethodStatement(testCase, genericMethod, calleeRef, argsRef, retRef)
            } else {
                +MethodStatement(testCase, genericMethod, calleeRef, argsRef)
            }
        }
    }

}