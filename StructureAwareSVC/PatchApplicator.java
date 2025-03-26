public class PatchApplicator<T> {
    public TreeNode<T> apply(Patch<T> patch, TreeNode<T> tree) {
        if (patch == null) return tree;

        switch (patch.type) {
            case NO_CHANGE:
                if (tree == null) return null;
                return new TreeNode<>(
                        tree.value,
                        apply(patch.leftPatch, tree.left),
                        apply(patch.rightPatch, tree.right)
                );

            case INSERT:
                return reconstruct(patch.target,
                        apply(patch.leftPatch, null),
                        apply(patch.rightPatch, null));

            case DELETE:
                // in Agda removal is handled by not rebuilding in serialize
                return null;

            case MODIFY:
                // handles both value and structural changes here
                TreeNode<T> newLeft = patch.leftPatch != null ?
                        apply(patch.leftPatch, tree != null ? tree.left : null) :
                        (tree != null ? tree.left : null);

                TreeNode<T> newRight = patch.rightPatch != null ?
                        apply(patch.rightPatch, tree != null ? tree.right : null) :
                        (tree != null ? tree.right : null);

                return new TreeNode<>(
                        patch.target != null ? patch.target.value :
                                (tree != null ? tree.value : null),
                        newLeft,
                        newRight
                );

            default:
                throw new IllegalArgumentException("Unknown patch type");
        }
    }

    private TreeNode<T> reconstruct(TreeNode<T> target, TreeNode<T> left, TreeNode<T> right) {
        if (target == null) return null;
        return new TreeNode<>(
                target.value,
                left != null ? left : target.left,
                right != null ? right : target.right
        );
    }
}