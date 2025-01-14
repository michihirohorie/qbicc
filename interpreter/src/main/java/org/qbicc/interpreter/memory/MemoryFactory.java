package org.qbicc.interpreter.memory;

import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodType;
import java.lang.invoke.VarHandle;
import java.nio.ByteOrder;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Function;

import org.eclipse.collections.api.RichIterable;
import org.eclipse.collections.api.factory.primitive.IntObjectMaps;
import org.eclipse.collections.api.map.primitive.MutableIntObjectMap;
import org.eclipse.collections.api.tuple.primitive.IntObjectPair;
import org.eclipse.collections.impl.map.mutable.ConcurrentHashMap;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.ConstantDynamic;
import org.objectweb.asm.FieldVisitor;
import org.objectweb.asm.Handle;
import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.qbicc.context.AttachmentKey;
import org.qbicc.context.CompilationContext;
import org.qbicc.interpreter.Memory;
import org.qbicc.interpreter.VmObject;
import org.qbicc.pointer.Pointer;
import org.qbicc.type.ArrayType;
import org.qbicc.type.BooleanType;
import org.qbicc.type.CompoundType;
import org.qbicc.type.FloatType;
import org.qbicc.type.IntegerType;
import org.qbicc.type.PointerType;
import org.qbicc.type.ReferenceType;
import org.qbicc.type.SignedIntegerType;
import org.qbicc.type.TypeType;
import org.qbicc.type.UnsignedIntegerType;
import org.qbicc.type.ValueType;
import org.qbicc.type.VoidType;

/**
 * Factory methods for producing memory instances.
 */
public final class MemoryFactory {

    private MemoryFactory() {}

    private static final Memory EMPTY = new ByteArrayMemory.LE(new byte[0]);

    /**
     * Get an empty memory.  The memory may have any type (or none) and is not guaranteed to be extendable or copyable.
     *
     * @return an empty memory (not {@code null})
     */
    public static Memory getEmpty() {
        return EMPTY;
    }

    public static Memory replicate(Memory first, int nCopies) {
        if (nCopies == 1) {
            return first;
        } else {
            return new VectorMemory(first, nCopies);
        }
    }

    public static Memory compose(Memory... memories) {
        if (memories == null || memories.length == 0) {
            return EMPTY;
        } else if (memories.length == 1) {
            return memories[0];
        } else {
            return new CompositeMemory(memories);
        }
    }

    /**
     * Wrap the given array as a memory of the same size and type.
     *
     * @param array the array to wrap (must not be {@code null})
     * @return the wrapper memory (must not be {@code null})
     */
    public static ByteArrayMemory wrap(byte[] array, ByteOrder byteOrder) {
        return byteOrder == ByteOrder.BIG_ENDIAN ? new ByteArrayMemory.BE(array) : new ByteArrayMemory.LE(array);
    }

    /**
     * Wrap the given array as a memory of the same size and type.
     *
     * @param array the array to wrap (must not be {@code null})
     * @return the wrapper memory (must not be {@code null})
     */
    public static ShortArrayMemory wrap(short[] array) {
        return new ShortArrayMemory(array);
    }

    /**
     * Wrap the given array as a memory of the same size and type.
     *
     * @param array the array to wrap (must not be {@code null})
     * @return the wrapper memory (must not be {@code null})
     */
    public static IntArrayMemory wrap(int[] array) {
        return new IntArrayMemory(array);
    }

    /**
     * Wrap the given array as a memory of the same size and type.
     *
     * @param array the array to wrap (must not be {@code null})
     * @return the wrapper memory (must not be {@code null})
     */
    public static LongArrayMemory wrap(long[] array) {
        return new LongArrayMemory(array);
    }

    /**
     * Wrap the given array as a memory of the same size and type.
     *
     * @param array the array to wrap (must not be {@code null})
     * @return the wrapper memory (must not be {@code null})
     */
    public static CharArrayMemory wrap(char[] array) {
        return new CharArrayMemory(array);
    }

    /**
     * Wrap the given array as a memory of the same size and type.
     *
     * @param array the array to wrap (must not be {@code null})
     * @return the wrapper memory (must not be {@code null})
     */
    public static FloatArrayMemory wrap(float[] array) {
        return new FloatArrayMemory(array);
    }

    /**
     * Wrap the given array as a memory of the same size and type.
     *
     * @param array the array to wrap (must not be {@code null})
     * @return the wrapper memory (must not be {@code null})
     */
    public static DoubleArrayMemory wrap(double[] array) {
        return new DoubleArrayMemory(array);
    }

    /**
     * Wrap the given array as a memory of the same size and type.
     *
     * @param array the array to wrap (must not be {@code null})
     * @return the wrapper memory (must not be {@code null})
     */
    public static BooleanArrayMemory wrap(boolean[] array) {
        return new BooleanArrayMemory(array);
    }

    /**
     * Wrap the given array as a memory of the same size and type.
     * The size of a reference is acquired from the given type.
     *
     * @param array the array to wrap (must not be {@code null})
     * @param refType the reference type (must not be {@code null})
     * @return the wrapper memory (must not be {@code null})
     */
    public static ReferenceArrayMemory wrap(VmObject[] array, ReferenceType refType) {
        return new ReferenceArrayMemory(array, refType);
    }

    static final class GenMemoryInfo {
        final String clazzName;
        final String clazzDesc;
        final Function<CompilationContext, Memory> producer;

        GenMemoryInfo(String clazzName, Function<CompilationContext, Memory> producer) {
            this.clazzName = clazzName;
            clazzDesc = "L" + clazzName + ";";
            this.producer = producer;
        }
    }

    private static final String CLASS_DESC_STR = Class.class.descriptorString();
    private static final String OBJECT_DESC_STR = Object.class.descriptorString();
    private static final String STRING_DESC_STR = String.class.descriptorString();
    private static final String LOOKUP_DESC_STR = MethodHandles.Lookup.class.descriptorString();
    private static final String PRIMITIVE_CLASS_DESC = "(" + LOOKUP_DESC_STR + STRING_DESC_STR + CLASS_DESC_STR + ")" + CLASS_DESC_STR;

    private static final AttachmentKey<Map<CompoundType, GenMemoryInfo>> MF_CACHE_KEY = new AttachmentKey<>();
    private static final String[] MEM_INTERFACES = { "org/qbicc/interpreter/Memory", "java/lang/Cloneable" };

    private static final AtomicLong seq = new AtomicLong();

    public static Function<CompilationContext, Memory> getMemoryFactory(CompilationContext ctxt, CompoundType ct, boolean upgradeLongs) {
        Map<CompoundType, GenMemoryInfo> map = ctxt.computeAttachmentIfAbsent(MF_CACHE_KEY, ConcurrentHashMap::new);
        // avoid constructing the lambda instance if possible
        GenMemoryInfo genMemoryInfo = map.get(ct);
        if (genMemoryInfo != null) {
            return genMemoryInfo.producer;
        }
        return map.computeIfAbsent(ct, ct1 -> makeFactory(ct1, upgradeLongs)).producer;
    }

    private static final Function<?, ?>[] NO_FUNCTIONS = new Function<?, ?>[0];

    private static GenMemoryInfo makeFactory(final CompoundType ct, boolean upgradeLongs) {
        // produce class per compound type
        MethodHandles.Lookup lookup = MethodHandles.lookup();
        ClassWriter cw = new ClassWriter(ClassWriter.COMPUTE_MAXS | ClassWriter.COMPUTE_FRAMES);

        String simpleName = "GenMemory";
        String clazzName = "org/qbicc/interpreter/memory/" + simpleName;

        cw.visit(Opcodes.V17, Opcodes.ACC_SUPER, clazzName, null, "org/qbicc/interpreter/memory/VarHandleMemory", MEM_INTERFACES);

        // emit size method
        MethodVisitor smv = cw.visitMethod(Opcodes.ACC_PUBLIC, "getSize", "()J", null, null);
        smv.visitCode();
        smv.visitLdcInsn(Long.valueOf(ct.getSize()));
        smv.visitInsn(Opcodes.LRETURN);
        smv.visitMaxs(0, 0);
        smv.visitEnd();

        // mapping of offset to condy for each simple field; the condy creates the VarHandle on demand

        final MutableIntObjectMap<ConstantDynamic> handles = IntObjectMaps.mutable.empty();

        // primitive type class condys
        ConstantDynamic booleanClassConstant = new ConstantDynamic("Z", CLASS_DESC_STR, new Handle(Opcodes.H_INVOKESTATIC, "java/lang/invoke/ConstantBootstraps", "primitiveClass", PRIMITIVE_CLASS_DESC, false));
        ConstantDynamic byteClassConstant = new ConstantDynamic("B", CLASS_DESC_STR, new Handle(Opcodes.H_INVOKESTATIC, "java/lang/invoke/ConstantBootstraps", "primitiveClass", PRIMITIVE_CLASS_DESC, false));
        ConstantDynamic shortClassConstant = new ConstantDynamic("S", CLASS_DESC_STR, new Handle(Opcodes.H_INVOKESTATIC, "java/lang/invoke/ConstantBootstraps", "primitiveClass", PRIMITIVE_CLASS_DESC, false));
        ConstantDynamic intClassConstant = new ConstantDynamic("I", CLASS_DESC_STR, new Handle(Opcodes.H_INVOKESTATIC, "java/lang/invoke/ConstantBootstraps", "primitiveClass", PRIMITIVE_CLASS_DESC, false));
        ConstantDynamic longClassConstant = new ConstantDynamic("J", CLASS_DESC_STR, new Handle(Opcodes.H_INVOKESTATIC, "java/lang/invoke/ConstantBootstraps", "primitiveClass", PRIMITIVE_CLASS_DESC, false));
        ConstantDynamic charClassConstant = new ConstantDynamic("C", CLASS_DESC_STR, new Handle(Opcodes.H_INVOKESTATIC, "java/lang/invoke/ConstantBootstraps", "primitiveClass", PRIMITIVE_CLASS_DESC, false));
        ConstantDynamic floatClassConstant = new ConstantDynamic("F", CLASS_DESC_STR, new Handle(Opcodes.H_INVOKESTATIC, "java/lang/invoke/ConstantBootstraps", "primitiveClass", PRIMITIVE_CLASS_DESC, false));
        ConstantDynamic doubleClassConstant = new ConstantDynamic("D", CLASS_DESC_STR, new Handle(Opcodes.H_INVOKESTATIC, "java/lang/invoke/ConstantBootstraps", "primitiveClass", PRIMITIVE_CLASS_DESC, false));

        // mapping of member to delegate Memory instance for each complex field

        Map<CompoundType.Member, String> delegate = null;

        Map<String, String> simpleFields = null;

        for (CompoundType.Member member : ct.getMembers()) {
            int offset = member.getOffset();
            String name = member.getName();
            String fieldName = name + '@' + offset;
            Class<?> fieldClazz;
            int fieldAccess;
            ValueType memberType = member.getType();
            if (memberType.getSize() == 0) {
                continue;
            }
            // complex fields
            if (memberType instanceof ArrayType || memberType instanceof CompoundType) {
                fieldAccess = Opcodes.ACC_PRIVATE | Opcodes.ACC_FINAL;
                if (delegate == null) {
                    delegate = new HashMap<>();
                }
                fieldClazz = Memory.class;
                delegate.put(member, fieldName);
            } else {
                // simple fields
                if (simpleFields == null) simpleFields = new LinkedHashMap<>();
                Object fieldTypeArg;
                fieldAccess = Opcodes.ACC_PRIVATE;
                if (memberType instanceof PointerType || upgradeLongs && memberType instanceof IntegerType it && it.getMinBits() == 64) {
                    fieldClazz = Pointer.class;
                    fieldTypeArg = Type.getType(fieldClazz);
                } else if (memberType instanceof IntegerType it) {
                    fieldClazz = switch (it.getMinBits()) {
                        case 8 -> byte.class;
                        case 16 -> it instanceof UnsignedIntegerType ? char.class : short.class;
                        case 32 -> int.class;
                        case 64 -> long.class;
                        default -> throw new IllegalStateException();
                    };
                    fieldTypeArg = switch (it.getMinBits()) {
                        case 8 -> byteClassConstant;
                        case 16 -> it instanceof UnsignedIntegerType ? charClassConstant : shortClassConstant;
                        case 32 -> intClassConstant;
                        case 64 -> longClassConstant;
                        default -> throw new IllegalStateException();
                    };
                } else if (memberType instanceof FloatType ft) {
                    fieldClazz = switch (ft.getMinBits()) {
                        case 32 -> float.class;
                        case 64 -> double.class;
                        default -> throw new IllegalStateException();
                    };
                    fieldTypeArg = switch (ft.getMinBits()) {
                        case 32 -> floatClassConstant;
                        case 64 -> doubleClassConstant;
                        default -> throw new IllegalStateException();
                    };
                } else if (memberType instanceof BooleanType) {
                    fieldClazz = boolean.class;
                    fieldTypeArg = booleanClassConstant;
                } else if (memberType instanceof TypeType) {
                    fieldClazz = ValueType.class;
                    fieldTypeArg = Type.getType(fieldClazz);
                } else if (memberType instanceof ReferenceType) {
                    fieldClazz = VmObject.class;
                    fieldTypeArg = Type.getType(fieldClazz);
                } else {
                    throw new IllegalStateException("Unknown type");
                }
                Handle bmh = new Handle(
                    Opcodes.H_INVOKESTATIC,
                    "java/lang/invoke/ConstantBootstraps",
                    "fieldVarHandle",
                    "("
                        + LOOKUP_DESC_STR
                        + STRING_DESC_STR
                        + CLASS_DESC_STR
                        + CLASS_DESC_STR
                        + CLASS_DESC_STR
                    + ")" + VarHandle.class.descriptorString(),
                    false
                );
                ConstantDynamic constant = new ConstantDynamic(fieldName, VarHandle.class.descriptorString(), bmh,
                    Type.getObjectType(clazzName),
                    fieldTypeArg
                );
                handles.put(offset, constant);
                simpleFields.put(fieldName, fieldClazz.descriptorString());
            }

            // instance field
            FieldVisitor fieldVisitor = cw.visitField(fieldAccess, fieldName, fieldClazz.descriptorString(), null, null);
            fieldVisitor.visitEnd();
        }

        // emit "getHandle" method
        String descriptor = "(I)" + VarHandle.class.descriptorString();
        MethodVisitor ghmv = ((ClassVisitor) cw).visitMethod(Opcodes.ACC_PROTECTED, "getHandle", descriptor, null, null);
        ghmv.visitParameter("offset", 0);
        ghmv.visitCode();// emit a switch statement to map offsets to condys
        Label noMatch = new Label();
        int cnt = handles.size();
        int[] keys = new int[cnt];
        Label[] labels = new Label[cnt];
        ConstantDynamic[] constants = new ConstantDynamic[cnt];
        int i = 0;
        RichIterable<IntObjectPair<ConstantDynamic>> iter = handles.keyValuesView();
        ArrayList<IntObjectPair<ConstantDynamic>> list = iter.into(new ArrayList<>());
        list.sort(Comparator.comparingInt(IntObjectPair::getOne));
        for (IntObjectPair<ConstantDynamic> pair : list) {
            keys[i] = pair.getOne();
            labels[i] = new Label();
            constants[i] = pair.getTwo();
            i++;
        }
        ghmv.visitVarInsn(Opcodes.ILOAD, 1); // offset
        ghmv.visitLookupSwitchInsn(noMatch, keys, labels);
        for (i = 0; i < cnt; i++) {
            ghmv.visitLabel(labels[i]);
            ghmv.visitLdcInsn(constants[i]);
            ghmv.visitInsn(Opcodes.ARETURN);
        }
        ghmv.visitLabel(noMatch);
        ghmv.visitVarInsn(Opcodes.ALOAD, 0); // this
        ghmv.visitVarInsn(Opcodes.ILOAD, 1); // offset
        ghmv.visitMethodInsn(Opcodes.INVOKESPECIAL, "org/qbicc/interpreter/memory/VarHandleMemory", "getHandle", descriptor, false);
        ghmv.visitInsn(Opcodes.ARETURN);
        ghmv.visitMaxs(0, 0);
        ghmv.visitEnd();

        // emit ctor
        MethodVisitor ctor = cw.visitMethod(0, "<init>", "(" + CompilationContext.class.descriptorString() + ")V", null, null);
        ctor.visitCode();
        ctor.visitVarInsn(Opcodes.ALOAD, 0);
        ctor.visitVarInsn(Opcodes.ALOAD, 1);
        ctor.visitMethodInsn(Opcodes.INVOKESPECIAL, "org/qbicc/interpreter/memory/VarHandleMemory", "<init>", "(" + CompilationContext.class.descriptorString() + ")V", false);

        // emit "clone" method
        MethodVisitor cmv = cw.visitMethod(Opcodes.ACC_PUBLIC, "clone", "()" + Memory.class.descriptorString(), null, null);
        cmv.visitCode();
        if (delegate == null) {
            // shallow clone, cool!
            cmv.visitVarInsn(Opcodes.ALOAD, 0);
            cmv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, "org/qbicc/interpreter/memory/AbstractMemory", "doClone", "()" + AbstractMemory.class.descriptorString(), false);
            cmv.visitInsn(Opcodes.ARETURN);
        } else {
            // deep clone :( emit a copy constructor and call it
            MethodVisitor ccmv = cw.visitMethod(Opcodes.ACC_PRIVATE, "<init>", "(" + Memory.class.descriptorString() + ")V", null, null);
            ccmv.visitParameter("orig", 0);
            ccmv.visitCode();
            // call super
            ccmv.visitVarInsn(Opcodes.ALOAD, 0); // this
            ccmv.visitVarInsn(Opcodes.ALOAD, 1); // this orig
            ccmv.visitTypeInsn(Opcodes.CHECKCAST, clazzName); // this orig'
            ccmv.visitInsn(Opcodes.DUP); // this orig' orig'
            ccmv.visitVarInsn(Opcodes.ASTORE, 1); // this orig'
            ccmv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, "org/qbicc/interpreter/memory/VarHandleMemory", "getCompilationContext", "()" + CompilationContext.class.descriptorString(), false); // orig' this cc
            ccmv.visitMethodInsn(Opcodes.INVOKESPECIAL, "org/qbicc/interpreter/memory/VarHandleMemory", "<init>", "(" + CompilationContext.class.descriptorString() + ")V", false); // orig'
            // shallow-copy all of the little fields
            if (simpleFields != null) for (Map.Entry<String, String> entry : simpleFields.entrySet()) {
                String fieldName = entry.getKey();
                String fieldDesc = entry.getValue();
                ccmv.visitVarInsn(Opcodes.ALOAD, 0);
                ccmv.visitVarInsn(Opcodes.ALOAD, 1);
                ccmv.visitFieldInsn(Opcodes.GETFIELD, clazzName, fieldName, fieldDesc);
                ccmv.visitFieldInsn(Opcodes.PUTFIELD, clazzName, fieldName, fieldDesc);
            }
            // deep-copy all of the sub-memories
            for (String fieldName : delegate.values()) {
                ccmv.visitVarInsn(Opcodes.ALOAD, 0);
                ccmv.visitVarInsn(Opcodes.ALOAD, 1);
                ccmv.visitFieldInsn(Opcodes.GETFIELD, clazzName, fieldName, Memory.class.descriptorString());
                ccmv.visitMethodInsn(Opcodes.INVOKEINTERFACE, "org/qbicc/interpreter/Memory", "clone", "()" + Memory.class.descriptorString(), true);
                ccmv.visitFieldInsn(Opcodes.PUTFIELD, clazzName, fieldName, Memory.class.descriptorString());
            }

            ccmv.visitInsn(Opcodes.RETURN);
            ccmv.visitMaxs(0, 0);
            ccmv.visitEnd();

            cmv.visitTypeInsn(Opcodes.NEW, clazzName);
            cmv.visitInsn(Opcodes.DUP);
            cmv.visitVarInsn(Opcodes.ALOAD, 0);
            cmv.visitMethodInsn(Opcodes.INVOKESPECIAL, clazzName, "<init>", "(" + Memory.class.descriptorString() + ")V", false);
            cmv.visitInsn(Opcodes.ARETURN);
        }
        cmv.visitMaxs(0, 0);
        cmv.visitEnd();

        Function<?, ?>[] factoryArray = NO_FUNCTIONS;
        // emit "getDelegateMemory" if needed
        if (delegate != null) {
            //java.lang.invoke.MethodHandles.classData
            factoryArray = new Function<?, ?>[delegate.size()];
            Handle classObjectBootstrap = new Handle(
                Opcodes.H_INVOKESTATIC,
                "java/lang/invoke/MethodHandles",
                "classData",
                "(" + LOOKUP_DESC_STR + STRING_DESC_STR + CLASS_DESC_STR + ")" + OBJECT_DESC_STR,
                false
            );
            ConstantDynamic factoryArrayConstant = new ConstantDynamic("_", OBJECT_DESC_STR, classObjectBootstrap);

            int fi = 0;
            //    protected Memory getDelegateMemory(int offset) {
            MethodVisitor mv = cw.visitMethod(Opcodes.ACC_PROTECTED, "getDelegateMemory", "(I)" + Memory.class.descriptorString(), null, null);
            mv.visitParameter("offset", 0);
            mv.visitCode();
            // now it's just there, on the stack

            for (Map.Entry<CompoundType.Member, String> entry : delegate.entrySet()) {
                CompoundType.Member member = entry.getKey();
                String fieldName = entry.getValue();
                Label outOfRange = new Label();
                // index < min || (min + size) <= index
                mv.visitVarInsn(Opcodes.ILOAD, 1);
                mv.visitLdcInsn(Integer.valueOf(member.getOffset()));
                mv.visitJumpInsn(Opcodes.IF_ICMPLT, outOfRange);
                mv.visitLdcInsn(Integer.valueOf((int) (member.getOffset() + member.getType().getSize())));
                mv.visitVarInsn(Opcodes.ILOAD, 1);
                mv.visitJumpInsn(Opcodes.IF_ICMPLE, outOfRange);
                mv.visitVarInsn(Opcodes.ALOAD, 0);
                mv.visitFieldInsn(Opcodes.GETFIELD, clazzName, fieldName, Memory.class.descriptorString());
                mv.visitInsn(Opcodes.ARETURN);
                mv.visitLabel(outOfRange);

                // also insert the init code for the field to the ctor
                Function<CompilationContext, Memory> factory = ctxt1 -> MemoryFactory.allocate(ctxt1, member.getType(), 1, upgradeLongs);
                factoryArray[fi] = factory;
                ctor.visitVarInsn(Opcodes.ALOAD, 0); // this
                ctor.visitLdcInsn(factoryArrayConstant); // this factoryArray
                ctor.visitTypeInsn(Opcodes.CHECKCAST, "[Ljava/util/function/Function;");
                ctor.visitLdcInsn(Integer.valueOf(fi)); // this factoryArray index
                ctor.visitInsn(Opcodes.AALOAD); // this factory
                ctor.visitVarInsn(Opcodes.ALOAD, 0); // this factory this
                ctor.visitMethodInsn(Opcodes.INVOKESPECIAL, "org/qbicc/interpreter/memory/VarHandleMemory", "getCompilationContext", "()" + CompilationContext.class.descriptorString(), false); // this factory ctxt
                ctor.visitMethodInsn(Opcodes.INVOKEINTERFACE, "java/util/function/Function", "apply", "(" + OBJECT_DESC_STR + ")" + OBJECT_DESC_STR, true); // this memory
                ctor.visitTypeInsn(Opcodes.CHECKCAST, "org/qbicc/interpreter/Memory");
                ctor.visitFieldInsn(Opcodes.PUTFIELD, clazzName, fieldName, Memory.class.descriptorString());
                fi ++;
            }
            // all out of range
            mv.visitInsn(Opcodes.ACONST_NULL);
            mv.visitInsn(Opcodes.ARETURN);
            mv.visitMaxs(0, 0);
            mv.visitEnd();
        }

        ctor.visitInsn(Opcodes.RETURN);
        ctor.visitMaxs(0, 0);
        ctor.visitEnd();
        cw.visitEnd();

        byte[] bytes = cw.toByteArray();
//        try {
//            Files.write(Paths.get("/tmp", simpleName + seq.getAndIncrement() + ".class"), bytes, StandardOpenOption.CREATE);
//        } catch (IOException ignored) {
//        }
        Class<? extends Memory> clazz;
        MethodHandles.Lookup hiddenClassLookup;
        try {
            hiddenClassLookup = lookup.defineHiddenClassWithClassData(bytes, factoryArray, false);
        } catch (IllegalAccessException e) {
            throw new IllegalStateException("Unexpected illegal access", e);
        }
        clazz = hiddenClassLookup.lookupClass().asSubclass(Memory.class);
        MethodHandle constructor;
        try {
            constructor = hiddenClassLookup.findConstructor(clazz, MethodType.methodType(void.class, CompilationContext.class));
        } catch (NoSuchMethodException | IllegalAccessException e) {
            throw new IllegalStateException("Unexpected failure finding constructor", e);
        }
        return new GenMemoryInfo(clazzName, ctxt -> {
            try {
                return (Memory) constructor.invoke(ctxt);
            } catch (Throwable e) {
                throw new IllegalStateException("Unexpected construction failure", e);
            }
        });
    }

    /**
     * Allocate a strongly typed memory with the given type and count.
     *
     * @param ctxt the compilation context (must not be {@code null})
     * @param type the type (must not be {@code null})
     * @param count the number of sequential elements to allocate
     * @param upgradeLongs {@code true} to upgrade {@code long} members to {@code Pointer} members, or {@code false} to
     *                     leave them as-is
     * @return the memory
     */
    public static Memory allocate(CompilationContext ctxt, ValueType type, long count, boolean upgradeLongs) {
        ByteOrder byteOrder = type.getTypeSystem().getEndianness();
        if (type instanceof VoidType || count == 0) {
            return getEmpty();
        }
        if (type instanceof ArrayType at) {
            long ec = count * at.getElementCount();
            if (ec > (1 << 30)) {
                // todo: we could vector some memories together...
                throw new IllegalArgumentException("too big");
            }
            ValueType et = at.getElementType();
            if (ec == 1) {
                return allocate(ctxt, et, 1, upgradeLongs);
            } else {
                return allocate(ctxt, et, ec, upgradeLongs);
            }
        }
        int intCount = Math.toIntExact(count);
        // vectored
        if (type instanceof CompoundType ct) {
            return getMemoryFactory(ctxt, ct, upgradeLongs).apply(ctxt);
        } else if (type instanceof IntegerType it) {
            // todo: more compact impls
            return switch (it.getMinBits()) {
                case 8 -> wrap(new byte[intCount], byteOrder);
                case 16 -> it instanceof SignedIntegerType ? wrap(new short[intCount]) : wrap(new char[intCount]);
                case 32 -> wrap(new int[intCount]);
                case 64 -> wrap(new long[intCount]);
                default -> throw new IllegalArgumentException();
            };
        } else if (type instanceof FloatType ft) {
            return switch (ft.getMinBits()) {
                case 32 -> wrap(new float[intCount]);
                case 64 -> wrap(new double[intCount]);
                default -> throw new IllegalArgumentException();
            };
        } else if (type instanceof BooleanType) {
            return wrap(new boolean[intCount]);
        } else {
            // todo: pointers, types
            throw new IllegalArgumentException();
        }
    }
}
