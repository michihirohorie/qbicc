package org.qbicc.machine.llvm.impl;

import java.util.List;

import org.qbicc.machine.llvm.Array;
import org.qbicc.machine.llvm.LLBasicBlock;
import org.qbicc.machine.llvm.LLBuilder;
import org.qbicc.machine.llvm.LLValue;
import org.qbicc.machine.llvm.Module;
import org.qbicc.machine.llvm.Struct;
import org.qbicc.machine.llvm.StructType;

/**
 *
 */
public final class LLVM {

    private LLVM() {}

    public static Module newModule() {
        return new ModuleImpl();
    }

    public static final LLValue i1 = new SingleWord("i1");
    public static final LLValue i8 = new SingleWord("i8");
    public static final LLValue i16 = new SingleWord("i16");
    public static final LLValue i24 = new SingleWord("i24");
    public static final LLValue i32 = new SingleWord("i32");
    public static final LLValue i64 = new SingleWord("i64");
    public static final LLValue i128 = new SingleWord("i128");

    public static final LLValue float16 = new SingleWord("half");
    public static final LLValue float32 = new SingleWord("float");
    public static final LLValue float64 = new SingleWord("double");
    public static final LLValue float128 = new SingleWord("fp128");

    public static final LLValue void_ = new SingleWord("void");

    public static final LLValue metadata = new MetadataType(null);

    public static final LLValue ZERO = new IntConstant(0);

    public static final LLValue FALSE = new SingleWord("false");
    public static final LLValue TRUE = new SingleWord("true");

    public static final LLValue NULL = new SingleWord("null");

    public static final LLValue zeroinitializer = new SingleWord("zeroinitializer");

    public static LLValue ptrTo(LLValue type, int addrSpace) {
        return new PointerTo((AbstractValue) type, addrSpace);
    }

    public static LLValue metadata(LLValue type) {
        return type == null ? metadata : new MetadataType((AbstractValue)type);
    }

    public static LLValue arrayType(int dimension, LLValue elementType) {
        return new ArrayType(dimension, (AbstractValue) elementType);
    }

    public static LLValue vector(final boolean vscale, final int dimension, final LLValue elementType) {
        return new VectorOf(dimension, (AbstractValue) elementType, vscale);
    }

    public static LLValue intConstant(int val) {
        return new IntConstant(val);
    }

    public static LLValue intConstant(long val) {
        return new LongConstant(val);
    }

    public static LLValue floatConstant(float val) {
        return new FloatConstant(val);
    }

    public static LLValue floatConstant(double val) {
        return new DoubleConstant(val);
    }

    public static LLValue bitcastConstant(LLValue val, LLValue fromType, LLValue toType) {
        return new BitcastConstant(val, fromType, toType);
    }

    public static LLValue addrspacecastConstant(LLValue val, LLValue fromType, LLValue toType) {
        return new AddrspacecastConstant(val, fromType, toType);
    }

    public static LLValue inttoptrConstant(LLValue val, LLValue fromType, LLValue toType) {
        return new IntToPtrConstant(val, fromType, toType);
    }

    public static LLValue ptrtointConstant(LLValue val, LLValue fromType, LLValue toType) {
        return new PtrToIntConstant(val, fromType, toType);
    }

    public static Array array(LLValue elementType) {
        return new ArrayImpl(elementType);
    }

    public static LLValue global(final String name) {
        return new NamedGlobalValueOf(name);
    }

    public static LLValue function(final LLValue returnType, final List<LLValue> argTypes, boolean variadic) {
        return new FunctionType(returnType, argTypes, variadic);
    }

    public static StructType structType() {
        return new StructTypeImpl();
    }

    public static Struct struct() {
        return new StructImpl();
    }

    public static LLValue metadataString(final String value) {
        return new MetadataString(value);
    }

    public static LLBuilder newBuilder(final LLBasicBlock block) {
        return new BuilderImpl((BasicBlockImpl) block);
    }

    public static LLValue byteArray(final byte[] contents) {
        return new ByteArrayImpl(contents);
    }
}