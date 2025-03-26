public class Patch<T> {
    public enum Type { NO_CHANGE, INSERT, DELETE, MODIFY }

    public final Type type;
    public final TreeNode<T> source;
    public final TreeNode<T> target;
    public final Patch<T> leftPatch;
    public final Patch<T> rightPatch;

    // For NO_CHANGE
    public Patch(Type type) {
        this(type, null, null, null, null);
    }

    // For INSERT/DELETE
    public Patch(Type type, TreeNode<T> source, TreeNode<T> target) {
        this(type, source, target, null, null);
    }

    // For MODIFY
    public Patch(Type type, TreeNode<T> source, TreeNode<T> target,
                 Patch<T> leftPatch, Patch<T> rightPatch) {
        this.type = type;
        this.source = source;
        this.target = target;
        this.leftPatch = leftPatch;
        this.rightPatch = rightPatch;
    }
}