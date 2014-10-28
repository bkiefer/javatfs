package de.dfki.lt.loot.tfs;

/** A class that provides empty implementations for all visitor methods of the
 *  DagVisitor, to override only those which are relevant.
 * 
 * @author kiefer
 */
public class DagVisitorAdapter implements DagVisitor {
  @Override
  public void startDag(DagNode here, DagNode deref, int corefNo) {}

  @Override
  public void visitEdge(DagNode deref, DagEdge edge) {}

  @Override
  public void endDag(DagNode deref) {}
}
