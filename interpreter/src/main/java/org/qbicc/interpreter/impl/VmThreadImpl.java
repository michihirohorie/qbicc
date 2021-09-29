package org.qbicc.interpreter.impl;

import org.qbicc.graph.MemoryAtomicityMode;
import org.qbicc.interpreter.VmThread;
import org.qbicc.interpreter.VmThrowable;
import org.qbicc.type.definition.element.FieldElement;

final class VmThreadImpl extends VmObjectImpl implements VmThread {
    final VmImpl vm;
    Frame currentFrame;

    VmThreadImpl(VmClassImpl clazz, VmImpl vm) {
        super(clazz);
        this.vm = vm;
    }

    @Override
    public VmImpl getVM() {
        return vm;
    }

    @Override
    public boolean isRunning() {
        return false;
    }

    @Override
    public boolean isFinished() {
        return false;
    }

    @Override
    public void await() {

    }

    void setThrown(final VmThrowable throwable) {
        FieldElement thrownField = vm.getCompilationContext().getExceptionField();
        int offset = getVmClass().getLayoutInfo().getMember(thrownField).getOffset();
        getMemory().storeRef(offset, throwable, MemoryAtomicityMode.NONE);
    }
}