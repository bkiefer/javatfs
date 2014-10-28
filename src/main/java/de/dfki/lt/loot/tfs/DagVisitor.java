package de.dfki.lt.loot.tfs;

public interface DagVisitor {
  
  /** called when node has been dereferenced and its coref no has been determined
   * 
   * @param here  the undereferenced dag
   * @param deref the dereferenced dag
   * @param corefNo the coref number, if any. If less than zero, this node
   *                is hit not for the first time, and after returning from
   *                this method, the recursive walk is stopped
   */
  public abstract void startDag(DagNode here, DagNode deref, int corefNo);
  
  /** called just before walking down the given edge
   * 
   * @param deref the dereferenced node
   * @param edge the edge that will execute a recursive call in the next step
   */
  public abstract void visitEdge(DagNode deref, DagEdge edge);
  
  /** called before returning from the current walk of the current node, after
   *  all edges have been visited.
   * 
   * @param deref the derefereced node
   */
  public abstract void endDag(DagNode deref);
}
