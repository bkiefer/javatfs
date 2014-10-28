package de.dfki.lt.loot.tfs;

import java.io.IOException;
import java.io.StringReader;
import java.io.Writer;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.Iterator;

import org.apache.log4j.Logger;

import de.dfki.lt.loot.tfs.io.InvalidSyntaxException;
import de.dfki.lt.loot.tfs.io.JxchgTokenizer;
import de.dfki.lt.loot.tfs.io.PetUndumper;

/** An adapter class for the different TFS implementations
 *
 *  Make sure that all methods which destructively change a TFS recompute
 *  the QC vector properly, because otherwise the hashCode fn will not work
 *  correctly.
 */
public class TFS {

  private static Logger logger = Logger.getLogger(TFS.class);

  private static DagNode qcSet;
  private static int qcLen;

  // leave this at -1 to indicate that it has not been set
  private int id = -1;

  DagNode val;
  private DagNode[] qcVector;
  private int[] argsQCVector;

  private static int transformQCDagRec(DagNode qcdag, int result) {
    int value = qcdag.getType();
    if (value != FSGrammar.TOP_TYPE) {
      String valString =
        DagNode.getGrammar().getTypeName(qcdag.getType());
      value = Integer.valueOf(valString.substring(1, valString.length() -1));
    }
    result = Math.max(result, value);
    qcdag.setType(value);
    Iterator<? extends DagEdge> arc1It = qcdag.getEdgeIterator();
    if (arc1It != null) {
      while (arc1It.hasNext()) {
        value = transformQCDagRec(arc1It.next().getValue(), result);
        result = Math.max(result, value);
      }
    }
    return result;
  }

  private static void getPetQCDag(FSGrammar gram) {
    TFS qcTFS = gram.getQCDag();
    if (qcTFS != null) {
      qcSet = qcTFS.dag().getValue(gram.getArgsFeature());
      qcLen = qcSet == null ? 0 : transformQCDagRec(qcSet, 0);
    }
  }

  public static void setGrammar(FSGrammar gram) {
    DagNode.setGrammar(gram);
    qcLen = 0;
    getPetQCDag(gram);
  }

  /** compute the (parent) qc vector for this dag and store it for future use */
  private void setQCVector() {
    if (qcLen > 0) {
      qcVector = new DagNode[qcLen];
      val.getQCVector(qcSet, qcVector);
    }
  }

  /** Set the dag slot of this TFS and compute the parent QC vector */
  private void setVal(DagNode aDag) {
    val = aDag;
    setQCVector();
  }

  private TFS(){}

  public TFS(DagNode sub) {
    setVal(sub);
  }

  public TFS(int typeID) {
    setVal(DagNode.buildFS(typeID));
  }

  /** Return the dag root node of this TFS */
  public DagNode dag() { return val; }

  /** Return the topmost type of this TFS */
  public int getType() { return val.getType(); }

  // public DagNode derefFS(DagNode dag) { return dag; }

  /** Return a clone of the current FS, i.e., an independent deep copy */
  public TFS cloneFS() { return new TFS(val.cloneFS()); }

  public boolean unifiable(TFS arg){ return val.isUnifiable(arg.val); }

  public TFS unifyFS(TFS arg) {
    DagNode resultDag = val.unifyFS(arg.val);
    return resultDag == null ? null : new TFS(resultDag);
  }

  public TFS unifyFS(TFS arg, int argNo) {
    DagNode resultDag = val.unifyFS(arg.val, argNo);
    return resultDag == null ? null : new TFS(resultDag);
  }

  public boolean unifyOnly(TFS arg, int argNo) {
    return dag().unifyOnly(arg.dag(), argNo);
  }

  public TFS copyResult(boolean deleteDaughters) {
    return new TFS(val.copyResult(deleteDaughters));
  }


  /** Copy a temporary dag, restricting while copying.
   *
   *  This is not in all cases equivalent to copying first and then applying
   *  the restrictor because
   * @param restrictor
   * @return
   */
  public TFS copyResult(TFS restrictor) {
    return new TFS(val.copyResult(restrictor.val));
  }

  @Override
  public boolean equals(Object obj) {
    if (! (obj instanceof TFS)) return false;
    return (this == obj) || val.equals(((TFS) obj).val);
  }

  public int subsumesBi(TFS arg) { return val.subsumesBi(arg.val); }

  public int countCorefs() {
    return val.countCorefs();
  }

  public int countCorefsRigid() {
    return val.countCorefsRigid();
  }

  public int countCorefsRigidSafe(IdentityHashMap<DagNode, Integer> result) {
    return val.countCorefsRigidSafe(result);
  }

  public int visited(DagNode node) {
    return node.visited();
  }

  public void deleteDaughters() {
    val.deleteDaughters();
  }

  /** This transforms a dag such that it can be used by the restrict(TFS r)
   *  method.
   * @return a copy of the incoming dag in which the types are massaged in a
   *         way that conforms to the restrict functionality.
   */
  public TFS getRestrictorDag() {
    DagNode restrictor = val.cloneFS();
    restrictor.transformRestrictorDag();
    TFS result = new TFS();
    result.val = restrictor;
    return result;
  }

  /** restrict a TFS, assuming it's a complete dag, given a restrictor dag */
  public void restrict(TFS restrictor) {
    val.restrict(restrictor.dag());
    setQCVector();
    invalidate();
  }

  /** restrict a TFS, assuming it's a complete dag, given a restrictor dag
   *  Recursively restrict a dag using a given restrictor dag
   *  The restrictor dag is a "pseudo dag", i.e., the types have special
   *  meanings.
   *
   *  Additionally, this restriction method deletes remaining edges in empty
   *  dlists, it deletes slash embeddings of a depth greater than
   *  MAX_SLASH_DEPTH and unfills.
   */
  public void restrictSpecial(TFS restrictor) {
    val.restrictSpecial(restrictor.dag());
    setQCVector();
    invalidate();
  }

  /** destructively remove all features marked in the grammar */
  public void restrict() {
    val.restrict();
    setQCVector();
  }

  /** Unfill the given TFS (destructively) */
  public void unfill() {
    val.unfill();
    setQCVector();
  }

  public DagNode getSubNode(Iterator<Short> path) {
    return val.getSubNode(path);
  }

  public int getArity() { return val.getArity(); }

  public TFS getNthArg(int argNo) {
    DagNode sub = val.getNthArg(argNo);
    return (sub == null ? null : new TFS(sub));
  }

  /** Return the key arg of this structure, or -1 if there is none */
  public int getKeyArg() {
    return val.getKeyArg();
  }


  public static TFS buildFS(JxchgTokenizer in)
  throws InvalidSyntaxException{
    TFS result = new TFS();
    try {
      result.setVal(DagNode.buildFS(in, result));
    } catch (IOException ioex) {
      result = null;
      logger.warn(ioex.getMessage());
    }
    return result;
  }

  public static TFS buildFS(PetUndumper undump) {
    TFS result = new TFS();
    result.setVal(DagNode.buildFS(undump));
    return result;
  }

  public static TFS fsFromString(String in) throws InvalidSyntaxException {
    return TFS.buildFS(new JxchgTokenizer(new StringReader(in)));
  }

  @Override
  public String toString() { return val.toString(); }

  @SuppressWarnings("static-access")
  public void invalidate() {
    val.invalidate();
  }

  public boolean subsumes(TFS fs) {
    return val.subsumes(fs.val);
  }

  /** Extract the type QC Vector for the given argument number. Since this must
   *  also work for intermediate dags, we have to extract the types and can not
   *  keep just the dag nodes.
   */
  public void setQCVector(int argNo) {
    if (argNo < 0) {
      setQCVector();
      return;
    }
    if (qcLen > 0) {
      argsQCVector = new int[qcLen];
      Arrays.fill(argsQCVector, FSGrammar.BOTTOM_TYPE);
      DagNode arg = val.getNthArg(argNo);
      if (arg != null) {
        DagNode[] argsDagQCVector = new DagNode[qcLen];
        arg.getQCVector(qcSet, argsDagQCVector);
        int i = 0;
        for (DagNode argsDag : argsDagQCVector) {
          if (argsDag == null) {
            argsQCVector[i] = FSGrammar.BOTTOM_TYPE;
          } else {
            argsQCVector[i] = argsDag.dereference().getNewType();
          }
          ++i;
        }
      }
    }
  }

  /** Is this (active, a.k.a. rule) TFS compatible with the given arg TFS, when
   *  only quick check vectors are concerned?
   *
  public boolean qcCompatible(TFS arg) {
    for (int pos = 0; pos < qcLen; ++pos) {
      DagNode argsDag = arg.qcVector[pos];
      if (argsDag != null
          && argsQCVector[pos] != FSGrammar.BOTTOM_TYPE
          && FSGrammar.BOTTOM_TYPE
             == DagNode.unifyTypes(argsQCVector[pos],
                                   argsDag.dereference().getNewType()))
        return false;
    }
    return true;
  }
  */

  /** Is this (active, a.k.a. rule) TFS compatible with the given arg TFS, when
   *  only quick check vectors are concerned?
   */
  public boolean qcCompatible(TFS arg) {
    for (int pos = 0; pos < qcLen; ++pos) {
      int argsType = arg.getQCType(pos);
      int parentType = argsQCVector[pos];
      if (argsType != FSGrammar.BOTTOM_TYPE
          && parentType != FSGrammar.BOTTOM_TYPE
          && FSGrammar.BOTTOM_TYPE == DagNode.unifyTypes(argsType, parentType))
        return false;
    }
    return true;
  }

  public static int getQCSize() {
    return qcLen;
  }

  public static DagNode getQCDag() {
    return qcSet;
  }

  public DagNode[] getQCDagVector() {
    // return the value of the pos'th element of the qc vector or -1
    return qcVector;
  }

  public int getQCType(int pos) {
    assert(pos < qcLen);
    // return the value of the pos'th element of the qc vector or -1
    return ((qcVector[pos] == null)
        ? FSGrammar.BOTTOM_TYPE
        : qcVector[pos].dereference().getNewType());
  }

  /** return the value of the pos'th element of the qc vector for the current
   *  argument of this TFS or -1
   */
  public int getArgQCType(int pos) {
    assert(pos < qcLen);
    return argsQCVector[pos] ;
  }

  @Override
  public int hashCode() {
    int result = 0;
    for (DagNode qcDag : qcVector) {
      result = result * 251 + ((qcDag == null) ? -1 : qcDag.getType());
    }
    return result;
  }

  public int getID() { return id; }
  public void setID(int i) { id = i; }

  public void write(Writer out) throws IOException {
    val.write(out);
  }

  /** return true if this TFS contains a cyclic dag, false otherwise */
  public boolean checkCycles() {
    return val.checkCycles();
  }

}
