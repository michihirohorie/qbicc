package org.qbicc.type.definition.element;

import org.qbicc.type.MethodType;
import org.qbicc.type.annotation.AnnotationValue;
import org.qbicc.type.definition.classfile.ClassFile;
import org.qbicc.type.descriptor.BaseTypeDescriptor;
import org.qbicc.type.descriptor.ClassTypeDescriptor;
import org.qbicc.type.descriptor.MethodDescriptor;
import org.qbicc.type.descriptor.TypeDescriptor;

/**
 * A method element.
 */
public abstract class MethodElement extends InvokableElement implements NamedElement {
    public static final MethodElement[] NO_METHODS = new MethodElement[0];

    /**
     * Special marker method used in method searches.
     */
    @SuppressWarnings("StaticInitializerReferencesSubClass")
    public static final MethodElement NOT_FOUND = new StaticMethodElement();
    /**
     * Special marker method used in method searches.
     */
    @SuppressWarnings("StaticInitializerReferencesSubClass")
    public static final MethodElement END_OF_SEARCH = new StaticMethodElement();

    private final String name;
    private final AnnotationValue defaultValue;

    MethodElement() {
        super();
        this.name = null;
        this.defaultValue = null;
    }

    MethodElement(BuilderImpl builder) {
        super(builder);
        this.name = builder.name;
        this.defaultValue = builder.defaultValue;
    }

    @Override
    public MethodType getType() {
        return (MethodType) super.getType();
    }

    @Override
    abstract MethodType computeType();

    public String toString() {
        TypeDescriptor desc = getEnclosingType().getDescriptor();
        if (desc instanceof ClassTypeDescriptor ctd) {
            final String packageName = ctd.getPackageName();
            if (packageName.isEmpty()) {
                return ctd.getClassName() + "." + getName() + getDescriptor();
            }
            return packageName + "." + ctd.getClassName() + "." + getName() + getDescriptor();
        } else if (desc instanceof BaseTypeDescriptor btd) {
            return btd.getFullName() + "." + getName() + getDescriptor();
        } else {
            throw new IllegalStateException();
        }
    }

    public String getName() {
        return name;
    }

    public AnnotationValue getDefaultValue() {
        return defaultValue;
    }

    public boolean isAbstract() {
        return hasAllModifiersOf(ClassFile.ACC_ABSTRACT);
    }

    public boolean isFinal() {
        return hasAllModifiersOf(ClassFile.ACC_FINAL);
    }

    public boolean isStatic() {
        return hasAllModifiersOf(ClassFile.ACC_STATIC);
    }

    public boolean isVirtual() {
        return hasNoModifiersOf(ClassFile.ACC_FINAL | ClassFile.ACC_PRIVATE | ClassFile.ACC_STATIC);
    }

    public boolean isNative() {
        return hasAllModifiersOf(ClassFile.ACC_NATIVE);
    }

    public boolean isSignaturePolymorphic() {
        return hasAllModifiersOf(ClassFile.I_ACC_SIGNATURE_POLYMORPHIC);
    }

    public <T, R> R accept(final ElementVisitor<T, R> visitor, final T param) {
        return visitor.visit(param, this);
    }

    public static Builder builder(String name, MethodDescriptor descriptor, int index) {
        return new BuilderImpl(name, descriptor, index);
    }

    public boolean overrides(final MethodElement other) {
        // todo: account for access control cases
        return ! isStatic()
            && ! other.isStatic()
            && ! other.isFinal()
            && getDescriptor().equals(other.getDescriptor())
            && getName().equals(other.getName())
            && getEnclosingType().load().getObjectType().isSubtypeOf(other.getEnclosingType().load().getObjectType());
    }

    public interface Builder extends InvokableElement.Builder, NamedElement.Builder {

        void setDefaultValue(AnnotationValue annotationValue);

        MethodElement build();

        interface Delegating extends InvokableElement.Builder.Delegating, NamedElement.Builder.Delegating, Builder {
            @Override
            Builder getDelegate();

            @Override
            default void setDefaultValue(AnnotationValue annotationValue) {
                getDelegate().setDefaultValue(annotationValue);
            }

            @Override
            default MethodElement build() {
                return getDelegate().build();
            }
        }
    }

    static final class BuilderImpl extends InvokableElement.BuilderImpl implements Builder {
        final String name;
        AnnotationValue defaultValue;

        BuilderImpl(String name, MethodDescriptor descriptor, int index) {
            super(descriptor, index);
            this.name = name;
        }

        public String getName() {
            return name;
        }

        public void setDefaultValue(AnnotationValue annotationValue) {
            this.defaultValue = annotationValue;
        }

        public MethodElement build() {
            return (modifiers & ClassFile.ACC_STATIC) != 0 ? new StaticMethodElement(this) : new InstanceMethodElement(this);
        }
    }
}
