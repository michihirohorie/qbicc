package cc.quarkus.qcc.tests.integration;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.nio.file.Path;

import cc.quarkus.qcc.context.DiagnosticContext;
import cc.quarkus.qcc.tests.integration.utils.TestConstants;
import cc.quarkus.qcc.tests.integration.utils.Javac;
import cc.quarkus.qcc.tests.integration.utils.NativeExecutable;
import cc.quarkus.qcc.tests.integration.utils.Qcc;
import org.jboss.logging.Logger;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

/**
 * Examples and Simple test apps to be built and tested for output.
 */
@Tag("simple-apps")
public class SimpleAppTest {

    private static final Logger LOGGER = Logger.getLogger(SimpleAppTest.class.getName());

    @Test
    public void helloWorld() throws IOException {
        String appName = "helloworld";
        Path appPath = Path.of(TestConstants.BASE_DIR).resolve("examples").resolve(appName);
        Path targetPath = Path.of(".").resolve("target");
        Path baseOutputPath = targetPath.resolve(appName);
        Path outputPath = baseOutputPath.resolve("classes");
        Path nativeOutputPath = baseOutputPath.resolve("native");
        Path source = appPath.resolve("hello/world/Main.java");
        String mainClass = "hello.world.Main";
        Path outputExecutable = nativeOutputPath.resolve("a.out");

        // Build via javac
        boolean compilationResult = Javac.compile(outputPath, source, LOGGER);

        assertTrue(compilationResult, "Compilation should succeed.");

        DiagnosticContext diagnosticContext = Qcc.build(outputPath, nativeOutputPath, mainClass, LOGGER);

        assertEquals(0, diagnosticContext.errors(), "Native image creation should generate no errors.");

        StringBuilder stdOut = new StringBuilder();
        StringBuilder stdErr = new StringBuilder();
        NativeExecutable.run(outputExecutable, stdOut, stdErr, LOGGER);

        assertTrue(stdErr.toString().isBlank(), "Native image execution should produce no error. " + stdErr);
        assertEquals("hello world", stdOut.toString().trim());
    }

    @Test
    public void branches() throws IOException {
        String appName = "branches";
        Path appPath = Path.of(".").resolve("apps").resolve(appName);
        Path targetPath = Path.of(".").resolve("target");
        Path baseOutputPath = targetPath.resolve(appName);
        Path outputPath = baseOutputPath.resolve("classes");
        Path nativeOutputPath = baseOutputPath.resolve("native");
        Path source = appPath.resolve("mypackage/Main.java");
        String mainClass = "mypackage.Main";
        Path outputExecutable = nativeOutputPath.resolve("a.out");

        // Build via javac
        boolean compilationResult = Javac.compile(outputPath, source, LOGGER);

        assertTrue(compilationResult, "Compilation should succeed.");

        DiagnosticContext diagnosticContext = Qcc.build(outputPath, nativeOutputPath, mainClass, LOGGER);

        assertEquals(0, diagnosticContext.errors(), "Native image creation should generate no errors.");

        StringBuilder stdOut = new StringBuilder();
        StringBuilder stdErr = new StringBuilder();
        NativeExecutable.run(outputExecutable, stdOut, stdErr, LOGGER);

        assertTrue(stdErr.toString().isBlank(), "Native image execution should produce no error. " + stdErr);
        assertEquals("1 1", stdOut.toString().trim());
    }

}