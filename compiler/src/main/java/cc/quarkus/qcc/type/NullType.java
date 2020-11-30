package cc.quarkus.qcc.type;

import io.smallrye.common.constraint.Assert;

/**
 * The type representing {@code null} literals, which is always {@code const} has no size and is incomplete.
 */
public final class NullType extends ValueType {
    NullType(final TypeSystem typeSystem) {
        super(typeSystem, NullType.class.hashCode(), true);
    }

    public boolean isComplete() {
        return false;
    }

    public long getSize() {
        return 0;
    }

    ValueType constructConst() {
        throw Assert.unreachableCode();
    }

    public NullType asConst() {
        return this;
    }

    public int getAlign() {
        return 0;
    }

    public boolean equals(final ValueType other) {
        return other instanceof NullType && super.equals(other);
    }

    public StringBuilder toString(final StringBuilder b) {
        return b.append("null");
    }

    public StringBuilder toFriendlyString(final StringBuilder b) {
        return b.append("null");
    }
}