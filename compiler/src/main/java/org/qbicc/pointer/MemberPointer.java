package org.qbicc.pointer;

import org.qbicc.interpreter.Memory;
import org.qbicc.type.CompoundType;

/**
 *
 */
public final class MemberPointer extends Pointer {
    private final Pointer structurePointer;
    private final CompoundType.Member member;

    public MemberPointer(Pointer structurePointer, CompoundType.Member member) {
        super(member.getType().getPointer());
        CompoundType pointeeType = (CompoundType) structurePointer.getType().getPointeeType();
        // todo: make it switchable if this makes things slow...
        if (! pointeeType.getMembers().contains(member)) {
            throw new IllegalArgumentException("Invalid pointer type");
        }
        this.structurePointer = structurePointer;
        this.member = member;
    }

    public Pointer getStructurePointer() {
        return structurePointer;
    }

    public CompoundType.Member getMember() {
        return member;
    }

    @Override
    public RootPointer getRootPointer() {
        return structurePointer.getRootPointer();
    }

    @Override
    public long getRootByteOffset() {
        return structurePointer.getRootByteOffset() + member.getOffset();
    }

    @Override
    public Memory getRootMemoryIfExists() {
        return structurePointer.getRootMemoryIfExists();
    }

    @Override
    public String getRootSymbolIfExists() {
        return structurePointer.getRootSymbolIfExists();
    }

    public <T, R> R accept(final Visitor<T, R> visitor, final T t) {
        return visitor.visit(t, this);
    }
}