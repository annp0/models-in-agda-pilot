import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class StructureAwareVCSTest {
    private final TreeNode<String> csvOriginal = new TreeNode<>("Alice",
            new TreeNode<>("440"),
            new TreeNode<>("7.0"));

    private <T> TreeNode<T> tree(T value, TreeNode<T> left, TreeNode<T> right) {
        return new TreeNode<>(value, left, right);
    }

    @Test
    void testNoChange() {
        Patch<String> patch = Diff.diff(csvOriginal, csvOriginal);
        assertEquals(Patch.Type.NO_CHANGE, patch.type);

        TreeNode<String> result = new PatchApplicator<String>().apply(patch, csvOriginal);
        assertEquals(csvOriginal.value, result.value);
    }

    @Test
    void testValueModification() {
        TreeNode<String> modified = tree("Bob", csvOriginal.left, csvOriginal.right);
        Patch<String> patch = Diff.diff(csvOriginal, modified);

        assertEquals(Patch.Type.MODIFY, patch.type);
        assertEquals("Alice", patch.source.value);
        assertEquals("Bob", patch.target.value);

        TreeNode<String> result = new PatchApplicator<String>().apply(patch, csvOriginal);
        assertEquals("Bob", result.value);
    }

    @Test
    void testInsertColumn() {
        TreeNode<String> modified = tree("Alice",
                tree("440",
                        new TreeNode<>("2023-09-15"),
                        null),
                csvOriginal.right);

        Patch<String> patch = Diff.diff(csvOriginal, modified);
        assertEquals(Patch.Type.MODIFY, patch.type);
        assertNotNull(patch.leftPatch);

        TreeNode<String> result = new PatchApplicator<String>().apply(patch, csvOriginal);
        assertEquals("2023-09-15", result.left.left.value); // New column exists
    }

    @Test
    void testTreeStructureChange() {
        TreeNode<String> leaf = new TreeNode<>("A");
        TreeNode<String> node = tree("A", new TreeNode<>("B"), null);

        Patch<String> patch = Diff.diff(leaf, node);
        assertEquals(Patch.Type.MODIFY, patch.type);
        assertNotNull(patch.leftPatch); // Structural change

        TreeNode<String> result = new PatchApplicator<String>().apply(patch, leaf);
        assertEquals("B", result.left.value);
    }

    @Test
    void testCombinedChanges() {
        TreeNode<String> original = tree("Root", null, null);
        TreeNode<String> modified = tree("NewRoot",
                new TreeNode<>("Left"),
                new TreeNode<>("Right"));

        Patch<String> patch = Diff.diff(original, modified);
        assertEquals(Patch.Type.MODIFY, patch.type);
        assertEquals("Root", patch.source.value);
        assertEquals("NewRoot", patch.target.value);
        assertNotNull(patch.leftPatch);
        assertNotNull(patch.rightPatch);

        TreeNode<String> result = new PatchApplicator<String>().apply(patch, original);
        assertEquals("NewRoot", result.value);
        assertEquals("Left", result.left.value);
        assertEquals("Right", result.right.value);
    }

    @Test
    void testDeleteSubtree() {
        TreeNode<String> original = tree("A",
                new TreeNode<>("B"),
                new TreeNode<>("C"));
        TreeNode<String> modified = tree("A", null, new TreeNode<>("C"));

        Patch<String> patch = Diff.diff(original, modified);
        assertEquals(Patch.Type.MODIFY, patch.type);
        assertEquals(Patch.Type.DELETE, patch.leftPatch.type);

        TreeNode<String> result = new PatchApplicator<String>().apply(patch, original);
        assertNull(result.left);
        assertEquals("C", result.right.value);
    }
}

