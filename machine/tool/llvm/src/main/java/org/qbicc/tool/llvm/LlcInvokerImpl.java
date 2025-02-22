package org.qbicc.tool.llvm;

import java.nio.file.Path;
import java.util.List;

import io.smallrye.common.constraint.Assert;
import io.smallrye.common.version.VersionScheme;
import org.qbicc.machine.arch.Platform;

/**
 *
 */
final class LlcInvokerImpl extends AbstractLlvmInvoker implements LlcInvoker {
    private LlcOptLevel optLevel = LlcOptLevel.O2;
    private OutputFormat outputFormat = OutputFormat.OBJ;
    private RelocationModel relocationModel = RelocationModel.Static;

    LlcInvokerImpl(final LlvmToolChainImpl tool, final Path path) {
        super(tool, path);
    }

    public LlvmToolChain getTool() {
        return super.getTool();
    }

    public void setOptimizationLevel(final LlcOptLevel level) {
        optLevel = Assert.checkNotNullParam("level", level);
    }

    public LlcOptLevel getOptimizationLevel() {
        return optLevel;
    }

    public void setOutputFormat(final OutputFormat outputFormat) {
        this.outputFormat = Assert.checkNotNullParam("outputFormat", outputFormat);
    }

    public OutputFormat getOutputFormat() {
        return outputFormat;
    }

    public void setRelocationModel(RelocationModel relocationModel) {
        this.relocationModel = Assert.checkNotNullParam("relocationModel", relocationModel);
    }

    public RelocationModel getRelocationModel() {
        return relocationModel;
    }

    void addArguments(final List<String> cmd) {
        Platform platform = getTool().getPlatform();
        cmd.add("-mtriple=" + platform.getCpu().toString() + "-" + platform.getOs().toString() + "-" + platform.getAbi().toString());
        cmd.add("--relocation-model=" + relocationModel.value);
        cmd.add("-" + optLevel.name());
        cmd.add("--filetype=" + outputFormat.toOptionString());
        cmd.add("--dwarf-version=4");
        if (VersionScheme.BASIC.compare(getTool().getVersion(), "14") >= 0) {
            cmd.add("--strict-dwarf");
        }
    }
}
