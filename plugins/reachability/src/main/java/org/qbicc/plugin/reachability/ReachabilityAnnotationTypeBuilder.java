package org.qbicc.plugin.reachability;

import org.qbicc.context.ClassContext;
import org.qbicc.type.annotation.Annotation;
import org.qbicc.type.definition.ConstructorResolver;
import org.qbicc.type.definition.DefinedTypeDefinition;
import org.qbicc.type.definition.FieldResolver;
import org.qbicc.type.definition.MethodResolver;
import org.qbicc.type.definition.element.ConstructorElement;
import org.qbicc.type.definition.element.FieldElement;
import org.qbicc.type.definition.element.MethodElement;
import org.qbicc.type.descriptor.ClassTypeDescriptor;
import org.qbicc.type.descriptor.MethodDescriptor;
import org.qbicc.type.descriptor.TypeDescriptor;

public class ReachabilityAnnotationTypeBuilder implements DefinedTypeDefinition.Builder.Delegating {
    private final DefinedTypeDefinition.Builder delegate;
    private final ReachabilityRoots roots;

    private final ClassTypeDescriptor autoQueued;
    private final ClassTypeDescriptor reflectivelyAccessed;

    public ReachabilityAnnotationTypeBuilder(final ClassContext classCtxt, DefinedTypeDefinition.Builder delegate) {
        this.delegate = delegate;
        this.roots = ReachabilityRoots.get(classCtxt.getCompilationContext());
        autoQueued = ClassTypeDescriptor.synthesize(classCtxt, "org/qbicc/runtime/AutoQueued");
        reflectivelyAccessed = ClassTypeDescriptor.synthesize(classCtxt, "org/qbicc/runtime/ReflectivelyAccessed");
    }

    @Override
    public DefinedTypeDefinition.Builder getDelegate() {
        return delegate;
    }

    @Override
    public void addMethod(MethodResolver resolver, int index, String name, MethodDescriptor descriptor) {
        Delegating.super.addMethod(new MethodResolver() {
            @Override
            public MethodElement resolveMethod(int index, DefinedTypeDefinition enclosing, MethodElement.Builder builder) {
                MethodElement methodElement = resolver.resolveMethod(index, enclosing, builder);
                for (Annotation annotation : methodElement.getInvisibleAnnotations()) {
                    if (annotation.getDescriptor().equals(autoQueued)) {
                        roots.registerAutoQueuedElement(methodElement);
                    } else if (annotation.getDescriptor().equals(reflectivelyAccessed)) {
                        roots.registerReflectiveMethod(methodElement);
                    }
                }
                return methodElement;
            }
        }, index, name, descriptor);
    }

    @Override
    public void addField(FieldResolver resolver, int index, String name, TypeDescriptor descriptor) {
        Delegating.super.addField(new FieldResolver() {
            @Override
            public FieldElement resolveField(int index, DefinedTypeDefinition enclosing, FieldElement.Builder builder) {
                FieldElement fieldElement = resolver.resolveField(index, enclosing, builder);
                for (Annotation annotation : fieldElement.getInvisibleAnnotations()) {
                    if (annotation.getDescriptor().equals(reflectivelyAccessed)) {
                       roots.registerReflectiveField(fieldElement);
                    }
                }
                return fieldElement;
            }
        }, index, name, descriptor);
    }

    @Override
    public void addConstructor(ConstructorResolver resolver, int index, MethodDescriptor descriptor) {
        Delegating.super.addConstructor(new ConstructorResolver() {
            @Override
            public ConstructorElement resolveConstructor(int index, DefinedTypeDefinition enclosing, ConstructorElement.Builder builder) {
                ConstructorElement constructorElement = resolver.resolveConstructor(index, enclosing, builder);
                for (Annotation annotation : constructorElement.getInvisibleAnnotations()) {
                    if (annotation.getDescriptor().equals(autoQueued)) {
                        roots.registerAutoQueuedElement(constructorElement);
                    } else if (annotation.getDescriptor().equals(reflectivelyAccessed)) {
                        roots.registerReflectiveConstructor(constructorElement);
                    }
                }
                return constructorElement;
            }
        }, index, descriptor);
    }
}
