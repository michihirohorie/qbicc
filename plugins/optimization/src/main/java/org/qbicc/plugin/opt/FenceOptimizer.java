package org.qbicc.plugin.opt;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.HashMap;
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
import org.qbicc.graph.CallNoSideEffects;
import org.qbicc.graph.CallNoReturn;
import org.qbicc.graph.ElementOf;
import org.qbicc.graph.Fence;
import org.qbicc.graph.FunctionHandle;
import org.qbicc.graph.FunctionDeclarationHandle;
import org.qbicc.graph.GlobalVariable;
import org.qbicc.graph.Invoke;
import org.qbicc.graph.InvokeNoReturn;
import org.qbicc.graph.Load;
import org.qbicc.graph.MemberOf;
import org.qbicc.graph.MemoryAtomicityMode;
import org.qbicc.graph.Node;
import org.qbicc.graph.PointerHandle;
import org.qbicc.graph.Store;
import org.qbicc.graph.TailCall;
import org.qbicc.graph.TailInvoke;
import org.qbicc.graph.Value;
import org.qbicc.graph.ValueHandle;
import org.qbicc.graph.Variable;
import org.qbicc.graph.VirtualMethodElementHandle;
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

import org.qbicc.plugin.dispatch.DispatchTables;
//import org.qbicc.driver.ClassContext;
import org.qbicc.type.definition.DefinedTypeDefinition;
import org.qbicc.type.definition.LoadedTypeDefinition;

import org.qbicc.plugin.reachability.RTAInfo;

import org.jboss.logging.Logger;


/**
 *
 */
public class FenceOptimizer implements Consumer<CompilationContext> {
    static final Logger logger = Logger.getLogger("org.qbicc.plugin.opt.fence");
    private FenceAnalyzerVisitor analyzer;
    private CompilationContext ctxt;
    private boolean foundSB;

    public void accept(final CompilationContext ctxt) {
        this.ctxt = ctxt;
        // Analyze
        analyzer = new FenceAnalyzerVisitor(ctxt);
        for (ProgramModule programModule : ctxt.getAllProgramModules()) {
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
                        try {
                            analyzer.execute(entryBlock, ((Function) item).getName());
                        } catch (FenceAnalyzerVisitor.TooBigException e) {
                            ctxt.warning("Element \"%s\" is too big. Abort fence optimization.", element);
                        }
                    }
                }
            }
        }

        // Analysis done. Call/Invoke related nodes are not resolved yet.
        Map<String, FenceAnalyzerVisitor.FunctionInfo> functionInfoMap = FenceAnalyzerVisitor.getAnalysis();

        foundSB = findSB(functionInfoMap);
        System.out.println("SB found?:" + foundSB);
        logger.debugf("SB:%d", foundSB);
        boolean foundIRIW = findIRIW(functionInfoMap);
        logger.debugf("IRIW:%d", foundIRIW);

        // Optimize
        for (String functionName : functionInfoMap.keySet()) {
            weaken(functionName, functionInfoMap.get(functionName));
        }
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
            if (blockInfo.isFailed()) {
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
                if (isFunctionCall(target)) {
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
     * Find the Store-Buffering (SB) pattern.
     *
     */
    private boolean findSB(Map<String, FenceAnalyzerVisitor.FunctionInfo> functionInfoMap) {
        Map<Store, Load> storeLoads = new HashMap<Store, Load>();

        // Collect sequences of store and load in the program order.
        for (String functionName : functionInfoMap.keySet()) {
            logger.debugf("Attempt to find the SB pattern %s", functionName);
            collectPotentialSB(functionInfoMap.get(functionName), storeLoads);
        }

        for (Store store1 : storeLoads.keySet()) {
            ValueHandle storeHandle1 = store1.getValueHandle();
            ValueHandle loadHandle1 = storeLoads.get(store1).getValueHandle();

            // Skip if loadHandle1 is equal to storeHandle1
            if (equals(storeHandle1, loadHandle1)) {
                continue;
            }

            for (Store store2 : storeLoads.keySet()) {
                ValueHandle storeHandle2 = store2.getValueHandle();
                ValueHandle loadHandle2 = storeLoads.get(store2).getValueHandle();

                if (equals(storeHandle2, loadHandle1) && equals(storeHandle1, loadHandle2)) {
                    return true;
                }
            }
        }

        return false;
    }
    
    /**
     * Find the Independent Reads of Independent Writes (IRIW) pattern.
     * 
     */
    private boolean findIRIW(Map<String, FenceAnalyzerVisitor.FunctionInfo> functionInfoMap) {
        Map<Load, Load> loadLoads = new HashMap<Load, Load>();
        Set<Store> stores = new HashSet<Store>();

        // Collect sequences of store and load in the program order.
        for (String functionName : functionInfoMap.keySet()) {
            logger.debugf("Attempt to find the IRIW pattern %s", functionName);
            collectPotentialIRIW(functionInfoMap.get(functionName), loadLoads, stores);
        }

        for (Load load1 : loadLoads.keySet()) {
            ValueHandle loadHandle1 = load1.getValueHandle();
            ValueHandle loadHandle2 = loadLoads.get(load1).getValueHandle();

            // Skip if loadHandle1 is equal to loadHandle2
            if (equals(loadHandle1, loadHandle2)) {
                continue;
            }

            for (Load load3 : loadLoads.keySet()) {
                ValueHandle loadHandle3 = load3.getValueHandle();
                ValueHandle loadHandle4 = loadLoads.get(load3).getValueHandle();
                
                if (equals(loadHandle1, loadHandle4) && equals(loadHandle2, loadHandle3)) {
                    boolean store1 = false;
                    boolean store2 = false;
                    for (Store store : stores) {
                        ValueHandle storeHandle = store.getValueHandle();
                        if (!store1 && equals(storeHandle, loadHandle1)) {
                            store1 = true;
                        }
                        if (!store2 && equals(storeHandle, loadHandle3)) {
                            store2 = true;
                        }
                        if (store1 && store2) {
                            return true;
                        }
                    }
                }
            }
        }

        return false;
    }

    private void collectPotentialSB(FenceAnalyzerVisitor.FunctionInfo functionInfo, Map<Store, Load> storeLoads) {
        Map<BasicBlock, FenceAnalyzerVisitor.BlockInfo> blockInfoMap = functionInfo.getMap();
        for (BasicBlock block : blockInfoMap.keySet()) {
            FenceAnalyzerVisitor.BlockInfo blockInfo = blockInfoMap.get(block);
            if (blockInfo.isFailed()) {
                logger.debugf("Couldn't get the information on fences in BasicBlock %s", block);
                continue;
            }
            List<Node> list = blockInfo.getList();
            if (list.size() == 0) {
                continue;
            }

            for (int i = list.size() - 1; i >= 0; --i) {
                Node target = list.get(i);
                if (!(target instanceof Load)) {
                    continue;
                }

                int j = i - 1;
                for (; j >= 0; --j) {
                    Node prev = list.get(j);
                    if (prev instanceof Load) {
                        break;
                    } else if (prev instanceof Store) {
                        storeLoads.put((Store)prev, (Load)target);
                    } else if (isFunctionCall(prev)) {
                        Object[] ret = new Object[1];
                        if (getIncomingIfFunctionCall(prev, ret)) {
                            Set<Node> set = (Set<Node>) ret[0];
                            if (set == null) {
                                continue;
                            }
                            for (Node p : set) {
                                if (p instanceof Store) {
                                    storeLoads.put((Store)p, (Load)target);
                                }
                            }
                        }
                    }
                }

                if (j < 0) {
                    Set<Node> incoming = blockInfo.getIncoming();
                    for (Node prev : incoming) {
                        if (prev instanceof Store) {
                            storeLoads.put((Store)prev, (Load)target);
                        }
                    }
                }
            }
        }
    }
    
    private void collectPotentialIRIW(FenceAnalyzerVisitor.FunctionInfo functionInfo, Map<Load, Load> loadLoads, Set<Store> stores) {
        Map<BasicBlock, FenceAnalyzerVisitor.BlockInfo> blockInfoMap = functionInfo.getMap();
        for (BasicBlock block : blockInfoMap.keySet()) {
            FenceAnalyzerVisitor.BlockInfo blockInfo = blockInfoMap.get(block);
            if (blockInfo.isFailed()) {
                logger.debugf("Couldn't get the information on fences in BasicBlock %s", block);
                continue;
            }
            List<Node> list = blockInfo.getList();
            if (list.size() == 0) {
                continue;
            }

            for (int i = list.size() - 1; i >= 0; --i) {
                Node target = list.get(i);
                if (target instanceof Store) 
                    stores.add((Store) target);
                if (!(target instanceof Load)) {
                    continue;
                }

                int j = i - 1;
                for (; j >= 0; --j) {
                    Node prev = list.get(j);
                    if (prev instanceof Store) {
                        break;
                    } else if (prev instanceof Load) {
                        loadLoads.put((Load)prev, (Load)target);
                    } else if (isFunctionCall(prev)) {
                        Object[] ret = new Object[1];
                        if (getIncomingIfFunctionCall(prev, ret)) {
                            Set<Node> set = (Set<Node>) ret[0];
                            if (set == null) {
                                continue;
                            }
                            for (Node p : set) {
                                if (p instanceof Load) {
                                    loadLoads.put((Load)p, (Load)target);
                                }
                            }
                        }
                    }
                }

                if (j < 0) {
                    Set<Node> incoming = blockInfo.getIncoming();
                    for (Node prev : incoming) {
                        if (prev instanceof Load) {
                            loadLoads.put((Load)prev, (Load)target);
                        }
                    }
                }
            }
        }
    }
    
    private boolean equals(ValueHandle v1, ValueHandle v2) {
        if (v1 instanceof GlobalVariable) {
            GlobalVariable v = (GlobalVariable) v1;
            return v.equals(v2); 
        } else if (v1 instanceof ElementOf) {
            ElementOf v = (ElementOf) v1;
            return v.equals(v2);
        } else if (v1 instanceof MemberOf) {
            MemberOf v = (MemberOf) v1;
            return v.equals(v2);
        }
        
        return false;
    }

    /**
     * Calculate tail nodes for a function after resolving Call/Invoke related nodes.
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
                if (blockInfo.isFailed()) {
                    functionInfo.setFailed();
                    return;
                }

                List<Node> list_returnBlock = blockInfo.getList();
                if (list_returnBlock == null) {
                    functionInfo.setFailed();
                    return;
                } else if (list_returnBlock.size() == 0) {
                    // Search incoming blocks of this block
                    Set<Node> set = findTail(block, functionName);
                    if (set == null) {
                        functionInfo.setFailed();
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
                        Object[] ret = new Object[1];
                        if (getIncomingIfFunctionCall(n, ret)) {
                            Set<Node> set = (Set<Node>) ret[0];
                            if (set == null) {
                                functionInfo.setFailed();
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
                            functionInfo.setFailed();
                            return;
                        }
                        if (set.size() == 0) {
                            noTail = true;
                        }
                        functionInfo.addTailNode(set);
                    }
                }
                if (functionInfo.getTailNodes().size() != 0 && noTail) {
                    functionInfo.setFailed();
                    return;
                }
            }
        }
    }

    /**
     *
     */
    private Set<Node> findTail(BasicBlock block, String functionName) {
        Set<Node> incomingSet = analyzer.getIncoming(block, functionName);

        if (incomingSet == null) {
            return null;
        } else if (incomingSet.size() == 0) {
            return Set.of();
        } else {
            Set<Node> functionCallFreeSet = new HashSet<Node>();
            for (Node n : incomingSet) {
                Object[] ret = new Object[1];
                if (getIncomingIfFunctionCall(n, ret)) {
                    Set<Node> set = (Set<Node>) ret[0];
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
        Object[] ret = new Object[1];
        if (getIncomingIfFunctionCall(prev, ret)) {
            Set<Node> set = (Set<Node>) ret[0];
            return weaken(node, set);
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
        if (!foundSB) {
            store.setMode(MemoryAtomicityMode.RELEASE);
            System.out.println("Done.");
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
                load.setMode(MemoryAtomicityMode.UNORDERED);
            }
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
                load.setMode(MemoryAtomicityMode.UNORDERED);
            }
        }

        return true;
    }

    private boolean weaken(Fence fence, Node prev) {
        if (prev instanceof Store) {
            Store prev_store = (Store) prev;
            //
            // prev_store
            // seq_cst
            //    +
            // release <- not needed
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
     * @return {@code true} if optimization should finish because of either successful optimization or
     *         giving up optimization due to some reasons, {@code false} otherwise .
     *
     */
    private boolean weaken(Node n, Set<Node> incomingSet) {
        if (incomingSet == null) {
            return true;
        }

        Set<Node> functionCallFreeSet = new HashSet<Node>();
        boolean isEmptySet = false;
        for (Node prev : incomingSet) {
            Object[] ret = new Object[1];
            if (getIncomingIfFunctionCall(prev, ret)) {
                Set<Node> set = (Set<Node>) ret[0];
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
            modeSet.add(getMode(prev));
        }

        if (modeSet.contains(MemoryAtomicityMode.RELEASE) && !modeSet.contains(MemoryAtomicityMode.ACQUIRE)) {
            // Weakest fence in modeSet is release. Check node n is also the release fence.
            if (n instanceof Fence) {
                Fence fence = (Fence) n;
                if (fence.getAtomicityMode() == MemoryAtomicityMode.RELEASE) {
                    fence.setAtomicityMode(MemoryAtomicityMode.UNORDERED);
                }
            }
        }

        if (modeSet.contains(MemoryAtomicityMode.ACQUIRE) && !modeSet.contains(MemoryAtomicityMode.RELEASE)) {
            // Weakest fence in modeSet is acquire. Check node n includes the acquire fence.
            if (n instanceof Load) {
                Load load = (Load) n;
                if (load.getMode() == MemoryAtomicityMode.ACQUIRE) {
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

    private boolean isFunctionCall(Node node) {
        return node instanceof Call
            || node instanceof CallNoSideEffects
            || node instanceof CallNoReturn
            || node instanceof TailCall
            || node instanceof Invoke
            || node instanceof InvokeNoReturn
            || node instanceof TailInvoke;
    }

    private boolean getIncomingIfFunctionCall(Node node, Object[] ret) {
        if (node instanceof Call) {
            ret[0] = getIncoming(((Call) node).getValueHandle());
            return true;
        } else if (node instanceof CallNoSideEffects) {
            ret[0] = getIncoming(((CallNoSideEffects) node).getValueHandle());
            return true;
        } else if (node instanceof CallNoReturn) {
            ret[0] = getIncoming(((CallNoReturn) node).getValueHandle());
            return true;
        } else if (node instanceof TailCall) {
            ret[0] = getIncoming(((TailCall) node).getValueHandle());
            return true;
        } else if (node instanceof Invoke) {
            ret[0] = getIncoming(((Invoke) node).getValueHandle());
            return true;
        } else if (node instanceof InvokeNoReturn) {
            ret[0] = getIncoming(((Invoke) node).getValueHandle());
            return true;
        } else if (node instanceof TailInvoke) {
            ret[0] = getIncoming(((Invoke) node).getValueHandle());
            return true;
        } else {
            return false;
        }
    }

    /**
     * @return a set of nodes after resolving Call/Invoke related nodes if it succeeded in
     * collecting incoming nodes, {@code null} otherwise.
     *
     */
    private Set<Node> getIncoming(ValueHandle valueHandle) {
        if (valueHandle instanceof PointerHandle) {
            MethodElement element = ctxt.getVirtualFunction(valueHandle);
            if (element == null) {
                return null;
            }
            String exactName = ctxt.getExactNameForElement(element, element.getType());
            String packageName = element.getEnclosingType().getDescriptor().getPackageName();
            String className = packageName.isEmpty()
                               ? element.getEnclosingType().getDescriptor().getClassName()
                               : packageName+"/"+element.getEnclosingType().getDescriptor().getClassName();
            DefinedTypeDefinition cls = ctxt.getBootstrapClassContext().findDefinedType(className);
            if (cls == null) {
                return null;
            }

            LoadedTypeDefinition loaded = cls.load();
            RTAInfo rtaInfo = RTAInfo.get(ctxt);
            List<String> subClassNames = new ArrayList<String>();
            Consumer<LoadedTypeDefinition> consumer = sub -> {
                String subTypeName = sub.getType().toString();
                subClassNames
                        .add(subTypeName.substring("class(".length(), subTypeName.length() - 1).replaceAll("/", "."));

            };

            rtaInfo.visitReachableSubclassesPreOrder(loaded, consumer);
            
            Map<String, FenceAnalyzerVisitor.FunctionInfo> functionInfoMap = FenceAnalyzerVisitor.getAnalysis();

            if (subClassNames.size() == 0) { // Only "exactName" is found as the potential callee
                FenceAnalyzerVisitor.FunctionInfo functionInfo = functionInfoMap.get(exactName);

                if (functionInfo == null) {
                    logger.debugf("No record on %s", exactName);
                    return null;
                }

                logger.debugf("Looking for record on %s", exactName);
                if (functionInfo.resolved()) {
                    return functionInfo.getTailNodes();
                }

                weaken(exactName, functionInfo);

                return functionInfo.getTailNodes();
            }

            // Multiple callees are found.
            Set<Node> incomings = new HashSet<Node>();
            for (String subClassName : subClassNames) {
                String methodName = exactName.replace(className.replaceAll("/", "."), subClassName);
                FenceAnalyzerVisitor.FunctionInfo functionInfo = functionInfoMap.get(methodName);

                if (functionInfo == null) {
                    logger.debugf("No record on %s", methodName);
                    return null;
                }

                logger.debugf("Looking for record on %s", methodName);
                if (functionInfo.resolved()) {
                    Set<Node> tailNodes = functionInfo.getTailNodes();
                    if (tailNodes == null) {
                        return null;
                    } else if (tailNodes.size() == 0) {
                        return Set.of();
                    }
                    incomings.addAll(tailNodes);
                } else {
                    weaken(methodName, functionInfo);

                    Set<Node> tailNodes = functionInfo.getTailNodes();
                    if (tailNodes == null) {
                        return null;
                    } else if (tailNodes.size() == 0) {
                        return Set.of();
                    }
                    incomings.addAll(tailNodes);
                }
            }

            return incomings;
        } else if (valueHandle instanceof FunctionHandle || valueHandle instanceof FunctionDeclarationHandle) {
            String callName = ((AbstractProgramObjectHandle) valueHandle).getProgramObject().getName();
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
        }

        return null;
    }
}
