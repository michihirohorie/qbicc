package org.qbicc.plugin.opt;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;

import org.qbicc.context.CompilationContext;
import org.qbicc.graph.AbstractProgramObjectHandle;
import org.qbicc.graph.BasicBlock;
import org.qbicc.graph.Call;
import org.qbicc.graph.Fence;
import org.qbicc.graph.FunctionHandle;
import org.qbicc.graph.FunctionDeclarationHandle;
import org.qbicc.graph.Load;
import org.qbicc.graph.MemberOf;
import org.qbicc.graph.MemoryAtomicityMode;
import org.qbicc.graph.Node;
import org.qbicc.graph.PointerHandle;
import org.qbicc.graph.Store;
import org.qbicc.graph.Value;
import org.qbicc.graph.ValueHandle;
import org.qbicc.graph.literal.SymbolLiteral;
import org.qbicc.object.Data;
import org.qbicc.object.DataDeclaration;
import org.qbicc.object.Function;
import org.qbicc.object.FunctionDeclaration;
import org.qbicc.object.ProgramModule;
import org.qbicc.object.ProgramObject;
import org.qbicc.object.Section;
import org.qbicc.type.FunctionType;
import org.qbicc.type.definition.MethodBody;
import org.qbicc.type.definition.element.ExecutableElement;
import org.qbicc.type.definition.element.MethodElement;

import org.jboss.logging.Logger;


/**
 * Optimization after the LOWER phase.
 *
 */
public class FenceOptimizer implements Consumer<CompilationContext> {
    static final Logger logger = Logger.getLogger("org.qbicc.plugin.opt.fence");

    public void accept(final CompilationContext compilationContext) {
        // Analyze
        List<ProgramModule> allProgramModules = compilationContext.getAllProgramModules();
        Iterator<ProgramModule> iterator = allProgramModules.iterator();
        compilationContext.runParallelTask(ctxt -> {
            for (;;) {
                ProgramModule programModule;
                synchronized (iterator) {
                    if (! iterator.hasNext()) {
                        return;
                    }
                    programModule = iterator.next();
                }

                FenceAnalyzerVisitor analyzer = new FenceAnalyzerVisitor(compilationContext);
                for (Section section : programModule.sections()) {
                    String sectionName = section.getName();
                    for (ProgramObject item : section.contents()) {
                        String name = item.getName();
                        if (item instanceof Function) {
                            ExecutableElement element = ((Function) item).getOriginalElement();
                            MethodBody body = ((Function) item).getBody();
                            boolean isExact = item == ctxt.getExactFunction(element);
                            if (body == null) {
                                ctxt.error("Function `%s` has no body", name);
                                continue;
                            }
                            BasicBlock entryBlock = body.getEntryBlock();
                            logger.debugf("Analyze %s", ((Function) item).getName());
                            analyzer.execute(entryBlock, ((Function) item).getName());
                        }
                    }
                }
                System.out.println("Done");
                // Analysis done. Call nodes are not resolved yet.
                Map<String, FenceAnalyzerVisitor.FunctionInfo> functionInfoMap = FenceAnalyzerVisitor.getAnalysis();

                // Optimize
                for (String functionName : functionInfoMap.keySet()) {
                    weaken(functionName, functionInfoMap.get(functionName));
                }
            }
        });

    }

    private void weaken(String functionName, FenceAnalyzerVisitor.FunctionInfo functionInfo) {
        if (functionInfo == null || functionInfo.isWeakening() || functionInfo.resolved()) {
            return;
        }
	functionInfo.setWeakening();

        logger.debugf("Attempt to optimize %s", functionName);
        Map<BasicBlock, FenceAnalyzerVisitor.BlockInfo> blockInfoMap = functionInfo.getMap();
        for (BasicBlock block : blockInfoMap.keySet()) {
            FenceAnalyzerVisitor.BlockInfo blockInfo = blockInfoMap.get(block);
            if (blockInfo.isFailedInfo()) {
                logger.debugf("Couldn't get the information on fences in BasicBlock %s", block);
                continue;
            }
            List<Node> list = blockInfo.getList();
            if (list.size() == 0) {
                continue;
            }

            // Try to weaken fences in a basic block.
            // A node will be weakened by checking previous nodes.
            for (int i = list.size() - 1; i >= 0; --i) {
                Node target = list.get(i);
                if (target instanceof Call) {
                    continue;
                }

                int j = i - 1;
                for (; j >= 0; --j) {
                    Node prev = list.get(j);
                    if (weaken(target, prev)) {
                        break;
                    }
                }

                if (j < 0) {
                    weaken(target, blockInfo.getIncoming());
                }
            }
        }

        addTail(functionName, functionInfo);

	functionInfo.setWeakened();
    }

    /**
     * Calculate tail nodes for a function after resolving Calls.
     *
     */
    private void addTail(String functionName, FenceAnalyzerVisitor.FunctionInfo functionInfo) {
        if (functionInfo.resolved()) {
            return;
        }

        Map<BasicBlock, FenceAnalyzerVisitor.BlockInfo> blockInfoMap = functionInfo.getMap();
        logger.debugf("Add tail nodes %s", functionName);
	boolean noTail = false;
        for (BasicBlock block : blockInfoMap.keySet()) {
            FenceAnalyzerVisitor.BlockInfo blockInfo = blockInfoMap.get(block);
            if (blockInfo.isReturnBlock()) {
                if (blockInfo.isFailedInfo()) {
		    functionInfo.setFail();
		    return;
                }

                List<Node> list_returnBlock = blockInfo.getList();
                if (list_returnBlock == null) {
                    functionInfo.setFail();
                    return; 
                } else if (list_returnBlock.size() == 0) {
                    // Search incoming blocks of this block
                    Set<Node> set = findTail(block, functionName);
		    if (set == null) {
                        functionInfo.setFail();
                        return; 
		    }
		    if (set.size() == 0) {
                        noTail = true;
		    }
		    functionInfo.addTailNode(set);
                } else {
                    // Return block has a list.
                    boolean foundTail = false;
		    for (int i = list_returnBlock.size() - 1; i >= 0; --i) {
                        Node n = list_returnBlock.get(i);
                        if (n instanceof Call) {
                            Set<Node> set = getIncoming((Call) n);
			    if (set == null) {
			        functionInfo.setFail();
                                return;
			    } else if (set.size() != 0) {
		                functionInfo.addTailNode(set);
                                foundTail = true;
			        break;
			    }
			} else {
		            functionInfo.addTailNode(n);
                            foundTail = true;
			    break;
			}
		    }
		    if (!foundTail) {
                        // Search incoming blocks of this block
                        Set<Node> set = findTail(block, functionName);
                        if (set == null) {
                            functionInfo.setFail();
                            return; 
                        }
			if (set.size() == 0) {
                            noTail = true;
			}
		        functionInfo.addTailNode(set);
		    }
                }
	        if (functionInfo.getTailNodes().size() != 0 && noTail) {
                    functionInfo.setFail();
		    return;
                }
	    }
        }
	if (functionInfo.getTailNodes() == null) {
//            System.out.println("Tail of " + functionName + " null");
	} else {
//	    System.out.println("Tail of " + functionName + " size=" + functionInfo.getTailNodes().size());
	}
    }

    /**
     *
     */
    private Set<Node> findTail(BasicBlock block, String functionName) {
        Set<Node> incomingSet = FenceAnalyzerVisitor.getIncoming(block, functionName);

        if (incomingSet == null) {
            return null;
        } else if (incomingSet.size() == 0) {
            return Set.of();
	} else {
            Set<Node> functionCallFreeSet = new HashSet<Node>();
            for (Node n : incomingSet) {
                if (n instanceof Call) {
                    Set<Node> set = getIncoming((Call) n);
                    if (set == null) {
                        return null;
                    }
                    if (set.size() == 0) {
                        return Set.of();
                    }
                    functionCallFreeSet.addAll(set);
                } else {
                    functionCallFreeSet.add(n);
                }
            }
	    return functionCallFreeSet;
        }
    }

    private boolean weaken(Node node, Node prev) {
        if (prev instanceof Call) {
            Set<Node> incoming = getIncoming((Call) prev);
            return weaken(node, incoming);
	}

        if (node instanceof Fence) {
	    return weaken((Fence) node, prev);
	} else if (node instanceof Load) {
	    return weaken((Load) node, prev);
	} else if (node instanceof Store) {
	    return weaken((Store) node, prev);
	}

	return false;
    }

    private boolean weaken(Store store, Node prev) {
        if (prev instanceof Store) {
            Store prev_store = (Store) prev;
            //
            // prev_store
	    //  seq_cst
	    //     +
            //  release   <- not needed
	    //   store
            //
            if (prev_store.getMode() == MemoryAtomicityMode.SEQUENTIALLY_CONSISTENT
                    && store.getMode() == MemoryAtomicityMode.RELEASE) {
                store.setMode(MemoryAtomicityMode.UNORDERED);
            }
        }

	return true;
    }

    private boolean weaken(Load load, Node prev) {
        if (prev instanceof Fence) {
            Fence prev_fence = (Fence) prev;
            //
            // acquire
	    //    +
            // acquire <- not needed
            //  load
            //
            // An acquire fence can be removed.
            //
            if (prev_fence.getAtomicityMode() == MemoryAtomicityMode.ACQUIRE
                    && load.getMode() == MemoryAtomicityMode.ACQUIRE) {
                System.out.println("OPT2");
                load.setMode(MemoryAtomicityMode.UNORDERED);
            }
            System.out.println("OPT2-2");
        } else if (prev instanceof Store) {
            Store prev_store = (Store) prev;
            //
            // prev_store
	    //  seq_cst
	    //    +
	    //  acquire   <- not needed
            //   load
            //
            if (prev_store.getMode() == MemoryAtomicityMode.SEQUENTIALLY_CONSISTENT
                    && load.getMode() == MemoryAtomicityMode.ACQUIRE) {
                System.out.println("OPT3");
                load.setMode(MemoryAtomicityMode.UNORDERED);
            }
            System.out.println("OPT3-2");
        }

	return true;
    }

    private boolean weaken(Fence fence, Node prev) {
	if (prev instanceof Store) {
            Store prev_store = (Store) prev;
            //
            // prev_store
	    //  seq_cst
	    //    +
            //  release   <- not needed
            //
            if (prev_store.getMode() == MemoryAtomicityMode.SEQUENTIALLY_CONSISTENT
                    && fence.getAtomicityMode() == MemoryAtomicityMode.RELEASE) {
                fence.setAtomicityMode(MemoryAtomicityMode.UNORDERED);
            }
        }

	return true;
    }

    /**
     * Try to weaken fence by calculating the weakest fence in the incoming set.
     *
     * @return true if optimization should finish because of either successful optimizaion or
     *         giving up optimization due to some reasons.
     *
     */
    private boolean weaken(Node n, Set<Node> incomingSet) {
        if (incomingSet == null) {
            return true;
        }

	Set<Node> functionCallFreeSet = new HashSet<Node>();
	boolean isEmptySet = false;
        for (Node prev : incomingSet) {
            if (prev instanceof Call) {
                Set<Node> set = getIncoming((Call) prev);
                if (set == null) { // Couldn't get the information. Give up optimizing node n.
                    return true;
                }
                if (set.size() == 0) { // No fence exists.
                    isEmptySet = true;
		    continue;
		}
	        functionCallFreeSet.addAll(set);
	    } else {
	        functionCallFreeSet.add(prev);
	    }
	}
        if (functionCallFreeSet.size() == 0) { // No node is found
            return false;
        } else if (isEmptySet) { // Set is not empty but at least a path has empty list. Should give up optimization.
            return true;
	}

        EnumSet<MemoryAtomicityMode> modeSet = EnumSet.noneOf(MemoryAtomicityMode.class);
        for (Node prev : functionCallFreeSet) {
            MemoryAtomicityMode mode = getMode(prev);
            if (mode == null) {
                return true;
            }
            modeSet.add(mode);
//            modeSet.add(getMode(prev));
        }

        if (modeSet.contains(MemoryAtomicityMode.RELEASE)
                && !modeSet.contains(MemoryAtomicityMode.ACQUIRE)) {
            // Weakest fence in modeSet is release. Check node n is also the release fence.
            if (n instanceof Fence) {
                Fence fence = (Fence) n;
                if (fence.getAtomicityMode() == MemoryAtomicityMode.RELEASE) {
                    fence.setAtomicityMode(MemoryAtomicityMode.UNORDERED);
                }
            }
        } 

	if (modeSet.contains(MemoryAtomicityMode.ACQUIRE)
                && !modeSet.contains(MemoryAtomicityMode.RELEASE)) {
            // Weakest fence in modeSet is acquire. Check node n includes the acquire fence.
            if (n instanceof Load) {
                Load load = (Load) n;
                if (load.getMode() == MemoryAtomicityMode.ACQUIRE) {
                    System.out.println("OPT4");
                    load.setMode(MemoryAtomicityMode.UNORDERED);
                }
            }
        }

        return true;
    }

    private MemoryAtomicityMode getMode(Node n) {
        if (n instanceof Fence) {
            return ((Fence) n).getAtomicityMode();
        } else if (n instanceof Load) {
            return ((Load) n).getMode();
        } else if (n instanceof Store) {
            return ((Store) n).getMode();
        } else {
            // Should not reach here
            return null;
	}
    }

    /**
     * @return a set of nodes after resolving Call nodes if it succeeded in collecting incoming nodes, {@code null} otherwise.
     *
     */
    private Set<Node> getIncoming(Call call) {

//        Value callTarget = call.getCallTarget();
	ValueHandle valueHandle = call.getValueHandle();

        if (valueHandle instanceof PointerHandle) {
            Value value = ((PointerHandle) valueHandle).getPointerValue();
	    System.out.println("name1=" + value);
        } else if (valueHandle instanceof FunctionHandle || valueHandle instanceof FunctionDeclarationHandle) {
            String name = ((AbstractProgramObjectHandle) valueHandle).getProgramObject().getName();
	    System.out.println("name2=" + name);
	}

	/*
        if (callTarget instanceof SymbolLiteral) { // TODO: support Load case
            String callName = ((SymbolLiteral) callTarget).getName();
            Map<String, FenceAnalyzerVisitor.FunctionInfo> functionInfoMap = FenceAnalyzerVisitor.getAnalysis();
            FenceAnalyzerVisitor.FunctionInfo functionInfo = functionInfoMap.get(callName);
            if (functionInfo == null) {
                logger.debugf("No record on %s", callName);
                return null;
            }

            logger.debugf("Looking for record on %s", callName);
	    if (functionInfo.resolved()) {
                return functionInfo.getTailNodes();
            }

	    weaken(callName, functionInfo);

	    return functionInfo.getTailNodes();
        } else {
            return null; // Currently just return null
	}
	*/
	return null;
    }
}
package org.qbicc.plugin.opt;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;

import org.qbicc.context.CompilationContext;
import org.qbicc.graph.AbstractProgramObjectHandle;
import org.qbicc.graph.BasicBlock;
import org.qbicc.graph.Call;
import org.qbicc.graph.Fence;
import org.qbicc.graph.FunctionHandle;
import org.qbicc.graph.FunctionDeclarationHandle;
import org.qbicc.graph.Load;
import org.qbicc.graph.MemberOf;
import org.qbicc.graph.MemoryAtomicityMode;
import org.qbicc.graph.Node;
import org.qbicc.graph.PointerHandle;
import org.qbicc.graph.Store;
import org.qbicc.graph.Value;
import org.qbicc.graph.ValueHandle;
import org.qbicc.graph.literal.SymbolLiteral;
import org.qbicc.object.Data;
import org.qbicc.object.DataDeclaration;
import org.qbicc.object.Function;
import org.qbicc.object.FunctionDeclaration;
import org.qbicc.object.ProgramModule;
import org.qbicc.object.ProgramObject;
import org.qbicc.object.Section;
import org.qbicc.type.FunctionType;
import org.qbicc.type.definition.MethodBody;
import org.qbicc.type.definition.element.ExecutableElement;
import org.qbicc.type.definition.element.MethodElement;

import org.jboss.logging.Logger;


/**
 * Optimization after the LOWER phase.
 *
 */
public class FenceOptimizer implements Consumer<CompilationContext> {
    static final Logger logger = Logger.getLogger("org.qbicc.plugin.opt.fence");

    public void accept(final CompilationContext compilationContext) {
        // Analyze
        List<ProgramModule> allProgramModules = compilationContext.getAllProgramModules();
        Iterator<ProgramModule> iterator = allProgramModules.iterator();
        compilationContext.runParallelTask(ctxt -> {
            for (;;) {
                ProgramModule programModule;
                synchronized (iterator) {
                    if (! iterator.hasNext()) {
                        return;
                    }
                    programModule = iterator.next();
                }

                FenceAnalyzerVisitor analyzer = new FenceAnalyzerVisitor(compilationContext);
                for (Section section : programModule.sections()) {
                    String sectionName = section.getName();
                    for (ProgramObject item : section.contents()) {
                        String name = item.getName();
                        if (item instanceof Function) {
                            ExecutableElement element = ((Function) item).getOriginalElement();
                            MethodBody body = ((Function) item).getBody();
                            boolean isExact = item == ctxt.getExactFunction(element);
                            if (body == null) {
                                ctxt.error("Function `%s` has no body", name);
                                continue;
                            }
                            BasicBlock entryBlock = body.getEntryBlock();
                            logger.debugf("Analyze %s", ((Function) item).getName());
                            analyzer.execute(entryBlock, ((Function) item).getName());
                        }
                    }
                }
                System.out.println("Done");
                // Analysis done. Call nodes are not resolved yet.
                Map<String, FenceAnalyzerVisitor.FunctionInfo> functionInfoMap = FenceAnalyzerVisitor.getAnalysis();

                // Optimize
                for (String functionName : functionInfoMap.keySet()) {
                    weaken(functionName, functionInfoMap.get(functionName));
                }
            }
        });

    }

    private void weaken(String functionName, FenceAnalyzerVisitor.FunctionInfo functionInfo) {
        if (functionInfo == null || functionInfo.isWeakening() || functionInfo.resolved()) {
            return;
        }
	functionInfo.setWeakening();

        logger.debugf("Attempt to optimize %s", functionName);
        Map<BasicBlock, FenceAnalyzerVisitor.BlockInfo> blockInfoMap = functionInfo.getMap();
        for (BasicBlock block : blockInfoMap.keySet()) {
            FenceAnalyzerVisitor.BlockInfo blockInfo = blockInfoMap.get(block);
            if (blockInfo.isFailedInfo()) {
                logger.debugf("Couldn't get the information on fences in BasicBlock %s", block);
                continue;
            }
            List<Node> list = blockInfo.getList();
            if (list.size() == 0) {
                continue;
            }

            // Try to weaken fences in a basic block.
            // A node will be weakened by checking previous nodes.
            for (int i = list.size() - 1; i >= 0; --i) {
                Node target = list.get(i);
                if (target instanceof Call) {
                    continue;
                }

                int j = i - 1;
                for (; j >= 0; --j) {
                    Node prev = list.get(j);
                    if (weaken(target, prev)) {
                        break;
                    }
                }

                if (j < 0) {
                    weaken(target, blockInfo.getIncoming());
                }
            }
        }

        addTail(functionName, functionInfo);

	functionInfo.setWeakened();
    }

    /**
     * Calculate tail nodes for a function after resolving Calls.
     *
     */
    private void addTail(String functionName, FenceAnalyzerVisitor.FunctionInfo functionInfo) {
        if (functionInfo.resolved()) {
            return;
        }

        Map<BasicBlock, FenceAnalyzerVisitor.BlockInfo> blockInfoMap = functionInfo.getMap();
        logger.debugf("Add tail nodes %s", functionName);
	boolean noTail = false;
        for (BasicBlock block : blockInfoMap.keySet()) {
            FenceAnalyzerVisitor.BlockInfo blockInfo = blockInfoMap.get(block);
            if (blockInfo.isReturnBlock()) {
                if (blockInfo.isFailedInfo()) {
		    functionInfo.setFail();
		    return;
                }

                List<Node> list_returnBlock = blockInfo.getList();
                if (list_returnBlock == null) {
                    functionInfo.setFail();
                    return; 
                } else if (list_returnBlock.size() == 0) {
                    // Search incoming blocks of this block
                    Set<Node> set = findTail(block, functionName);
		    if (set == null) {
                        functionInfo.setFail();
                        return; 
		    }
		    if (set.size() == 0) {
                        noTail = true;
		    }
		    functionInfo.addTailNode(set);
                } else {
                    // Return block has a list.
                    boolean foundTail = false;
		    for (int i = list_returnBlock.size() - 1; i >= 0; --i) {
                        Node n = list_returnBlock.get(i);
                        if (n instanceof Call) {
                            Set<Node> set = getIncoming((Call) n);
			    if (set == null) {
			        functionInfo.setFail();
                                return;
			    } else if (set.size() != 0) {
		                functionInfo.addTailNode(set);
                                foundTail = true;
			        break;
			    }
			} else {
		            functionInfo.addTailNode(n);
                            foundTail = true;
			    break;
			}
		    }
		    if (!foundTail) {
                        // Search incoming blocks of this block
                        Set<Node> set = findTail(block, functionName);
                        if (set == null) {
                            functionInfo.setFail();
                            return; 
                        }
			if (set.size() == 0) {
                            noTail = true;
			}
		        functionInfo.addTailNode(set);
		    }
                }
	        if (functionInfo.getTailNodes().size() != 0 && noTail) {
                    functionInfo.setFail();
		    return;
                }
	    }
        }
	if (functionInfo.getTailNodes() == null) {
//            System.out.println("Tail of " + functionName + " null");
	} else {
//	    System.out.println("Tail of " + functionName + " size=" + functionInfo.getTailNodes().size());
	}
    }

    /**
     *
     */
    private Set<Node> findTail(BasicBlock block, String functionName) {
        Set<Node> incomingSet = FenceAnalyzerVisitor.getIncoming(block, functionName);

        if (incomingSet == null) {
            return null;
        } else if (incomingSet.size() == 0) {
            return Set.of();
	} else {
            Set<Node> functionCallFreeSet = new HashSet<Node>();
            for (Node n : incomingSet) {
                if (n instanceof Call) {
                    Set<Node> set = getIncoming((Call) n);
                    if (set == null) {
                        return null;
                    }
                    if (set.size() == 0) {
                        return Set.of();
                    }
                    functionCallFreeSet.addAll(set);
                } else {
                    functionCallFreeSet.add(n);
                }
            }
	    return functionCallFreeSet;
        }
    }

    private boolean weaken(Node node, Node prev) {
        if (prev instanceof Call) {
            Set<Node> incoming = getIncoming((Call) prev);
            return weaken(node, incoming);
	}

        if (node instanceof Fence) {
	    return weaken((Fence) node, prev);
	} else if (node instanceof Load) {
	    return weaken((Load) node, prev);
	} else if (node instanceof Store) {
	    return weaken((Store) node, prev);
	}

	return false;
    }

    private boolean weaken(Store store, Node prev) {
        if (prev instanceof Store) {
            Store prev_store = (Store) prev;
            //
            // prev_store
	    //  seq_cst
	    //     +
            //  release   <- not needed
	    //   store
            //
            if (prev_store.getMode() == MemoryAtomicityMode.SEQUENTIALLY_CONSISTENT
                    && store.getMode() == MemoryAtomicityMode.RELEASE) {
                store.setMode(MemoryAtomicityMode.UNORDERED);
            }
        }

	return true;
    }

    private boolean weaken(Load load, Node prev) {
        if (prev instanceof Fence) {
            Fence prev_fence = (Fence) prev;
            //
            // acquire
	    //    +
            // acquire <- not needed
            //  load
            //
            // An acquire fence can be removed.
            //
            if (prev_fence.getAtomicityMode() == MemoryAtomicityMode.ACQUIRE
                    && load.getMode() == MemoryAtomicityMode.ACQUIRE) {
                System.out.println("OPT2");
                load.setMode(MemoryAtomicityMode.UNORDERED);
            }
            System.out.println("OPT2-2");
        } else if (prev instanceof Store) {
            Store prev_store = (Store) prev;
            //
            // prev_store
	    //  seq_cst
	    //    +
	    //  acquire   <- not needed
            //   load
            //
            if (prev_store.getMode() == MemoryAtomicityMode.SEQUENTIALLY_CONSISTENT
                    && load.getMode() == MemoryAtomicityMode.ACQUIRE) {
                System.out.println("OPT3");
                load.setMode(MemoryAtomicityMode.UNORDERED);
            }
            System.out.println("OPT3-2");
        }

	return true;
    }

    private boolean weaken(Fence fence, Node prev) {
	if (prev instanceof Store) {
            Store prev_store = (Store) prev;
            //
            // prev_store
	    //  seq_cst
	    //    +
            //  release   <- not needed
            //
            if (prev_store.getMode() == MemoryAtomicityMode.SEQUENTIALLY_CONSISTENT
                    && fence.getAtomicityMode() == MemoryAtomicityMode.RELEASE) {
                fence.setAtomicityMode(MemoryAtomicityMode.UNORDERED);
            }
        }

	return true;
    }

    /**
     * Try to weaken fence by calculating the weakest fence in the incoming set.
     *
     * @return true if optimization should finish because of either successful optimizaion or
     *         giving up optimization due to some reasons.
     *
     */
    private boolean weaken(Node n, Set<Node> incomingSet) {
        if (incomingSet == null) {
            return true;
        }

	Set<Node> functionCallFreeSet = new HashSet<Node>();
	boolean isEmptySet = false;
        for (Node prev : incomingSet) {
            if (prev instanceof Call) {
                Set<Node> set = getIncoming((Call) prev);
                if (set == null) { // Couldn't get the information. Give up optimizing node n.
                    return true;
                }
                if (set.size() == 0) { // No fence exists.
                    isEmptySet = true;
		    continue;
		}
	        functionCallFreeSet.addAll(set);
	    } else {
	        functionCallFreeSet.add(prev);
	    }
	}
        if (functionCallFreeSet.size() == 0) { // No node is found
            return false;
        } else if (isEmptySet) { // Set is not empty but at least a path has empty list. Should give up optimization.
            return true;
	}

        EnumSet<MemoryAtomicityMode> modeSet = EnumSet.noneOf(MemoryAtomicityMode.class);
        for (Node prev : functionCallFreeSet) {
            MemoryAtomicityMode mode = getMode(prev);
            if (mode == null) {
                return true;
            }
            modeSet.add(mode);
//            modeSet.add(getMode(prev));
        }

        if (modeSet.contains(MemoryAtomicityMode.RELEASE)
                && !modeSet.contains(MemoryAtomicityMode.ACQUIRE)) {
            // Weakest fence in modeSet is release. Check node n is also the release fence.
            if (n instanceof Fence) {
                Fence fence = (Fence) n;
                if (fence.getAtomicityMode() == MemoryAtomicityMode.RELEASE) {
                    fence.setAtomicityMode(MemoryAtomicityMode.UNORDERED);
                }
            }
        } 

	if (modeSet.contains(MemoryAtomicityMode.ACQUIRE)
                && !modeSet.contains(MemoryAtomicityMode.RELEASE)) {
            // Weakest fence in modeSet is acquire. Check node n includes the acquire fence.
            if (n instanceof Load) {
                Load load = (Load) n;
                if (load.getMode() == MemoryAtomicityMode.ACQUIRE) {
                    System.out.println("OPT4");
                    load.setMode(MemoryAtomicityMode.UNORDERED);
                }
            }
        }

        return true;
    }

    private MemoryAtomicityMode getMode(Node n) {
        if (n instanceof Fence) {
            return ((Fence) n).getAtomicityMode();
        } else if (n instanceof Load) {
            return ((Load) n).getMode();
        } else if (n instanceof Store) {
            return ((Store) n).getMode();
        } else {
            // Should not reach here
            return null;
	}
    }

    /**
     * @return a set of nodes after resolving Call nodes if it succeeded in collecting incoming nodes, {@code null} otherwise.
     *
     */
    private Set<Node> getIncoming(Call call) {

//        Value callTarget = call.getCallTarget();
	ValueHandle valueHandle = call.getValueHandle();

        if (valueHandle instanceof PointerHandle) {
            Value value = ((PointerHandle) valueHandle).getPointerValue();
	    System.out.println("name1=" + value);
        } else if (valueHandle instanceof FunctionHandle || valueHandle instanceof FunctionDeclarationHandle) {
            String name = ((AbstractProgramObjectHandle) valueHandle).getProgramObject().getName();
	    System.out.println("name2=" + name);
	}

	/*
        if (callTarget instanceof SymbolLiteral) { // TODO: support Load case
            String callName = ((SymbolLiteral) callTarget).getName();
            Map<String, FenceAnalyzerVisitor.FunctionInfo> functionInfoMap = FenceAnalyzerVisitor.getAnalysis();
            FenceAnalyzerVisitor.FunctionInfo functionInfo = functionInfoMap.get(callName);
            if (functionInfo == null) {
                logger.debugf("No record on %s", callName);
                return null;
            }

            logger.debugf("Looking for record on %s", callName);
	    if (functionInfo.resolved()) {
                return functionInfo.getTailNodes();
            }

	    weaken(callName, functionInfo);

	    return functionInfo.getTailNodes();
        } else {
            return null; // Currently just return null
	}
	*/
	return null;
    }
}
