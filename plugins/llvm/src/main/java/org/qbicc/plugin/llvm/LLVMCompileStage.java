package org.qbicc.plugin.llvm;

import java.nio.file.Path;
import java.util.Iterator;
import java.util.Map;
import java.util.function.Consumer;

import org.qbicc.context.CompilationContext;
import org.qbicc.type.definition.LoadedTypeDefinition;

public class LLVMCompileStage implements Consumer<CompilationContext> {
    private final boolean isPie;
    private final LLVMCompiler.Factory llvmCompilerFactory;

    public LLVMCompileStage(final boolean isPie, final LLVMCompiler.Factory llvmCompilerFactory) {
        this.isPie = isPie;
        this.llvmCompilerFactory = llvmCompilerFactory;
    }

    public void accept(final CompilationContext context) {
        LLVMState llvmState = context.getAttachment(LLVMState.KEY);
        if (llvmState == null) {
            context.note("No LLVM compilation units detected");
            return;
        }

        Iterator<Map.Entry<LoadedTypeDefinition, Path>> iterator = llvmState.getModulePaths().entrySet().iterator();
        context.runParallelTask(ctxt -> {
            LLVMCompiler compiler = llvmCompilerFactory.of(context, isPie);
            for (;;) {
                Map.Entry<LoadedTypeDefinition, Path> entry;
                synchronized (iterator) {
                    if (! iterator.hasNext()) {
                        return;
                    }
                    entry = iterator.next();
                }
                LoadedTypeDefinition typeDefinition = entry.getKey();
                Path modulePath = entry.getValue();
                compiler.compileModule(ctxt, typeDefinition, modulePath);
            }
        });
    }
}
