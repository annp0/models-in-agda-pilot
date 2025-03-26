public class Diff {
    public static <T> Patch<T> diff(TreeNode<T> t1, TreeNode<T> t2) {
        if (t1 == null && t2 == null) return new Patch<>(Patch.Type.NO_CHANGE);
        if (t1 == null) return new Patch<>(Patch.Type.INSERT, null, t2);
        if (t2 == null) return new Patch<>(Patch.Type.DELETE, t1, null);

        Patch<T> leftPatch = diff(t1.left, t2.left);
        Patch<T> rightPatch = diff(t1.right, t2.right);

        //  create MODIFY if values differ, regardless of subtrees
        if (!t1.value.equals(t2.value)) {
            return new Patch<>(Patch.Type.MODIFY, t1, t2, leftPatch, rightPatch);
        }
        //  use NO_CHANGE if absolutely nothing changed
        else if (leftPatch.type == Patch.Type.NO_CHANGE &&
                rightPatch.type == Patch.Type.NO_CHANGE) {
            return new Patch<>(Patch.Type.NO_CHANGE);
        }
        else {
            // value same but subtrees changed -> MODIFY with original values
            return new Patch<>(Patch.Type.MODIFY, t1, t2, leftPatch, rightPatch);
        }
    }
}
