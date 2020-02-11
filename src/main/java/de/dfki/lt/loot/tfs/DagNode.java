package de.dfki.lt.loot.tfs;

import gnu.trove.set.hash.TShortHashSet;

import java.io.IOException;
import java.io.StreamTokenizer;
import java.io.StringWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;

import de.dfki.lt.loot.tfs.io.DagPrinter;
import de.dfki.lt.loot.tfs.io.InvalidSyntaxException;
import de.dfki.lt.loot.tfs.io.JxchgTokenizer;
import de.dfki.lt.loot.tfs.io.PetUndumper;
import de.dfki.lt.loot.tfs.util.IntTrie;
import de.dfki.lt.loot.tfsdebugging.ErrorProducer;


/** This is a class for typed feature structures, represented as dags
 *
 *  Included is a Tomabechi style unifier a la PET, (bidirectional) subsumption,
 *  failure recording for these operations, JXCHG reading and printing,
 *  PET binary dumping and undumping, and support for Quick Check
 *
 *  This class depends on an FSGrammar class to provide, e.g., type unification
 *  and type and feature name mapping, constants for special purpose
 *  substructures like ARGS lists, etc.
 *
 *  A dag from this class can NOT be used for unification or subsumption in
 *  more that one thread simultaneously because of the scratch slots which are
 *  guarded by a static generation counter. Moreover, the generation counters
 *  would have to be thread-local to allow to use it in parallel threads even
 *  with completely independent structures.
 *
 *  In this implementation, the edge lists must be sorted according to the
 *  feature ids to work properly.
 */
public class DagNode {

  public static Map<DagNode, FailType> forwardFailures =
    new IdentityHashMap<DagNode, FailType>();
  public static Map<DagNode, FailType> backwardFailures =
    new IdentityHashMap<DagNode, FailType>();

  public static final int THIS_MORE_GENERAL = 1;
  public static final int ARG_MORE_GENERAL = 2;

  protected static boolean recordFailures = false;

  protected static final int THIS_MORE_GENERAL_MASK = ~ THIS_MORE_GENERAL;
  protected static final int ARG_MORE_GENERAL_MASK = ~ ARG_MORE_GENERAL;

  protected static FSGrammar fsgrammar;

  protected static short NO_FEAT = Short.MAX_VALUE;
  protected static short ARGS_FEATURE;
  protected static short FIRST_FEATURE;
  protected static short REST_FEATURE;

  // TODO: very special constant, for grammar approximation
  protected static short SLASH_FEATURE;
  protected static int MAX_SLASH_DEPTH = 999; // TODO: maybe even only 3

  // A marker dag for cycle checks
  private static final DagNode INSIDE = new DagNode(0);

  // only fore reading statistics
  public static int totalNoNodes = 0, totalNoArcs = 0;

  // throw an error if reading a jxchg file with an unknown feature
  public static boolean UNKNOWN_FEATURE_ERROR = true;

  // these two would have to be thread-local for this class to be used in
  // parallel threads
  private static long currentGenerationMax = 1;
  private static long currentGeneration = 1;

  @SuppressWarnings("serial")
  private class CycleError extends Error {}

  /* ******************** PUBLIC CONSTANTS AND VARIABLES ******************** */

  /** Use internal codes or external names for printing */
  public static boolean PRINT_READABLE = true;

  /** A printer used to change the default toString method to print the right
   *  format
   */
  private static DagPrinter _DEFAULT_PRINTER = null;

  /** Which type of failure occured?
   *  unification failures: Type clash, cycle, wellformedness unification
   *  subsumption failures: type mismatch, missing feature, missing variable
   */
  public enum FailType { SUCCESS, TYPE, CYCLE, FEATURE, VARIABLE, WELLFORMED }

  /** Restrictor constants, with the following meaning (in the restrictor dag)
   *  KEEP: keep only the features mentioned in this restrictor node, with the
   *      the exception of those that point to DEL nodes
   *  DEL: remove the feature pointing to this node in the parent
   *  NO: delete only features pointing to a DEL restrictor node, otherwise,
   *      recurse into subdags
   *  The FULL value (leave this node as is, stop recursion here) can be
   *  achieved by using KEEP and having no outgoing edges in that restrictor
   *  node)
   */
  public enum RESTRICT { RSTR_KEEP, RSTR_DEL, RSTR_NO }

  // if this is non-null, count statistics about type failures are collected
  static public IntTrie<int[]> paths;

  /* ******************** PRIVATE FIELDS AND CLASSES ******************** */

  // The type of this node
  private int _typeCode;
  // The feature-value list
  private ArrayList<DagEdge> _edges;

  // a generation counter to (in)validate the following scratch fields
  private long _generation;
  // these are the generation-protected scratch slots
  private int _newType;
  private DagNode _forward;
  private DagNode _copy;
  private ArrayList<DagEdge> _compArcs;


  /** so that we don't have to return null when the edges list is empty */
  private static Iterator<DagEdge> emptyEdges =
    new Iterator<DagEdge>() {
    public boolean hasNext() { return false; }
    public DagEdge next() { throw new NoSuchElementException(); }
    public void remove() {
      throw new UnsupportedOperationException();
    }
  };

  /** This iterator iterates over the edges of a node correctly, be it a
   * `complete' or `temporary' dag, i.e., one that is currently involved in
   * unification as has a maybe non-empty compArcs list.
   */
  class EdgeIterator {
    private int cursorArcs = -1;
    private int cursorCompArcs = -1;

    EdgeIterator() {
      if (DagNode.this._edges != null) {	//
        if (DagNode.this._edges.isEmpty()) {
          DagNode.this._edges = null;
          cursorArcs = -1;
        } else {
          cursorArcs = 0;
        }
      }
      cursorCompArcs = (_generation == currentGeneration &&
                        DagNode.this._compArcs != null) ? 0 : -1 ;
    }

    public boolean hasNext() {
      return cursorArcs != -1 || cursorCompArcs != -1;
    }

    public DagEdge next() {
      if (cursorArcs != -1) {
        // cursorArcs != -1
        if (cursorCompArcs == -1 ||
            (DagNode.this._compArcs.get(cursorCompArcs).feature >
             DagNode.this._edges.get(cursorArcs).feature)) {
          int curr = cursorArcs++;
          if (cursorArcs == DagNode.this._edges.size()) {
            cursorArcs = -1;
          }
          return DagNode.this._edges.get(curr);
        }
      }
      // if (cursorCompArcs == -1) throw new NoSuchElementException();
      int curr = cursorCompArcs++;
      if (cursorCompArcs == DagNode.this._compArcs.size()) {
        cursorCompArcs = -1;
      }
      return DagNode.this._compArcs.get(curr);
    }

    public void add(DagEdge arc) {
      if (cursorCompArcs != -1) {
        // add it at the cursor and move it to the next element.
        if (cursorCompArcs == 0 ||
            (DagNode.this._compArcs.get(cursorCompArcs - 1).feature
             < arc.feature)) {
          DagNode.this._compArcs.add(cursorCompArcs, arc);
        } else {
          DagNode.this._compArcs.add(cursorCompArcs - 1, arc);
        }
        ++cursorCompArcs;
      } else {
        // if cursorCompArcs is -1, it is ALWAYS at the end of the compArcs
        // list, either because the list was empty in the beginning, or the
        // compArcs have all been visited. Otherwise, the cursor would have a
        // non-negative value.
        if (DagNode.this._compArcs == null) {
          DagNode.this._compArcs = new ArrayList<DagEdge>();
          DagNode.this._compArcs.add(arc);
        } else {
          int lastIndex =  DagNode.this._compArcs.size() - 1;
          if (DagNode.this._compArcs.get(lastIndex).feature > arc.feature) {
            DagNode.this._compArcs.add(lastIndex, arc);
          } else {
            DagNode.this._compArcs.add(arc);
          }
        }
      }
      /*
        int i = 0;
        while (i < DagNode.this.compArcs.size()) {
        if (i > 0 &&
        DagNode.this.compArcs.get(i-1).feature >=
        DagNode.this.compArcs.get(i).feature) {
        System.out.println("what");
        }
        ++i;
        }
      */
    }
  }


  public static void invalidate() {
    if (currentGeneration > currentGenerationMax)
      currentGenerationMax = currentGeneration;
    currentGeneration = ++currentGenerationMax;
  }

  protected DagNode(int typeIdent) {
    _typeCode = typeIdent;
    _edges = null;
    _generation = 0;
  }

  // *************************************************************************
  // Operations specific to tomabechi dag representation
  // *************************************************************************

  protected DagNode dereference() {
    if (_generation != currentGeneration || _forward == null) return this;
    return _forward.dereference();
  }

  public void setForward(DagNode fs) {
    if (_generation != currentGeneration) {
      _newType = _typeCode;
      _copy = null;
      _compArcs = null;
      _generation = currentGeneration;
    }
    _forward = fs;
  }

  public DagNode getForward() {
    return (_generation != currentGeneration) ? null :
      this._forward;
  }

  private void setCopy(DagNode fs) {
    if (_generation != currentGeneration) {
      _newType = _typeCode;
      _forward = null;
      _compArcs = null;
      _generation = currentGeneration;
    }
    _copy = fs;
  }

  private DagNode getCopy() {
    return (_generation != currentGeneration) ? null : this._copy;
  }

  /** An iterator that works for complete as well as transitional (unified
   *  but not copied) dags correctly.
   *  Printers may have to have access to this special iterator, therefore
   *  the visibility is default.
   * @return An iterator iterating over all edges of this dag
   */
  EdgeIterator getNewEdgeIterator() {
    return this.new EdgeIterator();
  }

  public boolean newEdgesAreEmpty() {
    return (_edges == null &&
            ((_generation != currentGeneration) || this._compArcs == null));
  }

  public int getNewType() {
    return (_generation != currentGeneration) ? this._typeCode : this._newType;
  }

  private void setNewType(int what) {
    if (_generation != currentGeneration) {
      _forward = null;
      _copy = null;
      _compArcs = null;
      _generation = currentGeneration;
    }
    _newType = what;
  }

  public void setVisited(int what) { setNewType(what); }

  public int visited() {
    if (_generation != currentGeneration) return -1;
    return _newType;
  }

  // *************************************************************************
  // END Operations specific to tomabechi dag representation
  // *************************************************************************

  public int getType() {
    return this._typeCode;
  }

  public void setType(int typeIdent) {
    this._typeCode = typeIdent;
  }

  public String getTypeName() {
    int aType = this.getNewType();
    String name = fsgrammar.getTypeName(aType);
    if (name == null)
      return "UNK_" + aType;
    if (aType < fsgrammar.getNoOfTypes())
      return name;
    return "@"+name+"@";
  }

  public static void setGrammar(FSGrammar grammar) {
    fsgrammar = grammar;
    ARGS_FEATURE = grammar.getArgsFeature();
    FIRST_FEATURE = grammar.getFirstFeature();
    REST_FEATURE = grammar.getRestFeature();
    SLASH_FEATURE = grammar.getFeatureId("SLASH");
  }

  public static FSGrammar getGrammar() { return fsgrammar; }

  /** does typeId1 subsumes (is more general than or equal to) typeId2 */
  public static boolean subsumesType(int typeId1, int typeId2) {
    return fsgrammar.subsumesType(typeId1, typeId2);
  }

  /** does typeId1 subsumes (is more general than or equal to) typeId2 */
  public static int unifyTypes(int typeId1, int typeId2) {
    return fsgrammar.unifyTypes(typeId1, typeId2);
  }

  public static void recordFailures(boolean state) {
    recordFailures = state;
  }

  public static void registerPrinter(DagPrinter printer) {
    _DEFAULT_PRINTER = printer;
  }

  private DagNode cloneFSRec() {
    DagNode newCopy = getCopy();
    if (newCopy == null) {
      newCopy = new DagNode(getNewType());
      setCopy(newCopy);
      if (getEdges() != null) {
        for (DagEdge e : getEdges()) {
          newCopy.addEdge(e.feature, e.value.cloneFSRec());
        }
      }
    }
    return newCopy;
  }

  /** create an independent clone of the current dag (a deep copy) */
  public DagNode cloneFS() {
    invalidate();
    return cloneFSRec();
  }


  private DagNode copyFsRec(TShortHashSet featuresToDelete,
      int[] typesToGeneralize) {
    DagNode newCopy = getCopy();
    if (newCopy == null) {
      if (typesToGeneralize != null) {
        int fsType = getNewType();
        for (int type : typesToGeneralize) {
          if (type != fsType && subsumesType(type, fsType)) {
            fsType = type;
            break;
          }
        }
      }
      newCopy = new DagNode(getNewType());
      setCopy(newCopy);
      if (getEdges() != null) {
        for (DagEdge e : getEdges()) {
          if (! featuresToDelete.contains(e.feature))
            newCopy.addEdge(e.feature,
                e.value.copyFsRec(featuresToDelete, typesToGeneralize));
        }
      }
    }
    return newCopy;
  }

  /** create an independent clone of the current dag (a deep copy) */
  public DagNode copyFs(TShortHashSet featuresToDelete, int[] typesToGeneralize) {
    invalidate();
    return copyFsRec(featuresToDelete, typesToGeneralize);
  }

  public DagNode derefFS() {
    return dereference();
  }

  /** recursive helper function for copyResult()
   *  This does *NOT* implement partial copying, so the resulting dag will be
   *  completely independent of the unified source structures, which makes it
   *  safe to use them in a parallel execution environment, as long as it's not
   *  during unification
   */
  private DagNode copyResultRec() {
    DagNode in = this.dereference();
    DagNode newCopy = in.getCopy();
    if (newCopy == INSIDE) {
      throw new CycleError();
    }
    if (newCopy != null) {
      return newCopy;
    }

    newCopy = new DagNode(in.getNewType());
    in.setCopy(INSIDE);

    int newsize = 0;
    int cursorArcs = -1, cursorCompArcs = -1;
    if (in._edges != null) {
      cursorArcs = 0;
      newsize = in._edges.size();
    }
    if (_generation == currentGeneration && in._compArcs != null) {
      cursorCompArcs = 0;
      newsize += in._compArcs.size();
    }

    if (cursorArcs != -1 || cursorCompArcs != -1) {
      newCopy._edges = new ArrayList<DagEdge>(newsize);
    }
    while (cursorArcs != -1 || cursorCompArcs != -1) {
      DagEdge arc = null ;
      if (cursorArcs != -1 &&
          (cursorCompArcs == -1
           || (in._compArcs.get(cursorCompArcs).feature
               > in._edges.get(cursorArcs).feature))) {
        int curr = cursorArcs;
        if (++cursorArcs == in._edges.size()) {
          cursorArcs = -1;
        }
        arc = in._edges.get(curr);
      } else {
        int curr = cursorCompArcs;
        if (++cursorCompArcs == in._compArcs.size()) {
          cursorCompArcs = -1;
        }
        arc = in._compArcs.get(curr);
      }

      short feat = arc.feature;
      newCopy._edges.add(new DagEdge(feat, arc.value.copyResultRec()));
    }
    newCopy.edgesAreEmpty();
    in.setCopy(newCopy);
    in._compArcs = null;
    // if resetting the copy slot is really necessary, it must be done AFTER
    // copying has finished in a new recursive walkthrough
    //in.setCopy(null);
    return newCopy;
  }

  /** Copy the result after a series of unifications.
   *
   *  This does *NOT* implement partial copying, so the resulting dag will be
   *  completely independent of the unified source structures, which makes it
   *  safe to use them in a parallel execution environment, as long as it's not
   *  during unification
   *
   *  @return a copied result independent from the input dag
   */
  public DagNode copyResult() {
    // Return a copied result using the scratch buffer of this node
    DagNode result = null;
    try {
      result = copyResultRec();
    } catch (CycleError err) {
      result = null;
    }
    invalidate();
    return result;
  }


  /** recursive helper function for copyResult() */
  @SuppressWarnings("null")
  private DagNode copyResultRec(DagNode restrictor, TShortHashSet toDelete) {
    DagNode in = this.dereference();
    DagNode newCopy = in.getCopy();
    if (newCopy != null) {
      // this is less efficient, but guarantees equal results to copy first
      // - restrict later
      //if (restrictor != null) {
      //  // destructively change new dag
      //  newCopy.restrict(restrictor);
      //}
      return newCopy;
    }

    RESTRICT restr = RESTRICT.RSTR_NO;
    Iterator<DagEdge> restIt = null;
    DagEdge restArc = null;
    if (restrictor != null) {
      restr = restrictor.getRestrictorType();
      restIt = restrictor.getEdgeIterator();
      if (restIt.hasNext()) {
        restArc = restIt.next();
      }
    }

    newCopy = new DagNode(in.getNewType());
    in.setCopy(newCopy);

    int newsize = 0;
    int cursorArcs = -1, cursorCompArcs = -1;
    if (in._edges != null) {
      cursorArcs = 0;
      newsize = in._edges.size();
    }
    if (_generation == currentGeneration && in._compArcs != null) {
      cursorCompArcs = 0;
      newsize += in._compArcs.size();
    }

    if (cursorArcs != -1 || cursorCompArcs != -1) {
      newCopy._edges = new ArrayList<DagEdge>(newsize);
    }
    while (cursorArcs != -1 || cursorCompArcs != -1) {
      DagEdge arc = null ;
      if (cursorArcs != -1 &&
          (cursorCompArcs == -1
           || (in._compArcs.get(cursorCompArcs).feature
               > in._edges.get(cursorArcs).feature))) {
        int curr = cursorArcs;
        if (++cursorArcs == in._edges.size()) {
          cursorArcs = -1;
        }
        arc = in._edges.get(curr);
      } else {
        int curr = cursorCompArcs;
        if (++cursorCompArcs == in._compArcs.size()) {
          cursorCompArcs = -1;
        }
        arc = in._compArcs.get(curr);
      }

      short feat = arc.feature;
      while (restArc != null && restArc.feature < feat) {
        restArc = restIt.hasNext() ? restIt.next() : null;
      }
      DagNode subRestr = null;
      if (restArc != null && restArc.feature == feat) {
        subRestr = restArc.value;
      }
      boolean keep =
          ((toDelete == null) || ! toDelete.contains(feat))
          && ((restr == RESTRICT.RSTR_NO
               && (subRestr == null
                   || subRestr.getType() != RESTRICT.RSTR_DEL.ordinal()))
              || (restr == RESTRICT.RSTR_KEEP && subRestr != null
                  && restArc.feature == feat));
      if (keep) {
        newCopy._edges.add(
            new DagEdge(feat, arc.value.copyResultRec(subRestr, toDelete)));
      }
    }
    newCopy.edgesAreEmpty();
    in._compArcs = null;
    // if resetting the copy slot is really necessary, it must be done AFTER
    // copying has finished in a new recursive walkthrough
    //in.setCopy(null);
    return newCopy;
  }

  /*
  public class Massager {
    private static Massager

    int restr;
    TShortHashSet toDelete;
    public void startNode() {}
    Massager nextFeat(short feature) { return null; }
    boolean keep() {
      boolean keep =
          ((toDelete == null) || ! toDelete.contains(feature))
          && ((restr == RESTRICT.RSTR_NO
              && (subRestr == null || subRestr.getType() != RESTRICT.RSTR_DEL.ordinal()))
                 || (restr == RESTRICT.RSTR_KEEP && subRestr != null
                 && restArc.feature == feat));
      return keep;
    }
    Massager descend() { return null; }
  }
  */

  /** recursive helper function for copyResult(), massager version */
  DagNode copyResultRec(DagRestrictor m) {
    DagNode in = this.dereference();
    DagNode newCopy = in.getCopy();
    if (newCopy == INSIDE) {
      throw new CycleError();
    }
    if (newCopy != null) {
      // this is less efficient, but guarantees equal results to copy first
      // - restrict later
      /*
      if (restrictor != null) {
        // destructively change new dag
        newCopy.restrict(restrictor);
      }
      */
      return newCopy;
    }

    int newType = in.getNewType();
    if (m != null) newType = m.massageType(newType);

    newCopy = new DagNode(newType);

    // first check if this is an empty DLIST that should be massaged
    if (fsgrammar.subsumesType(fsgrammar.dListTypeId, getType())) {
      /*
      DagNode list = getValue(fsgrammar.listFeatureId);
      DagNode last = getValue(fsgrammar.lastFeatureId);
      if (list != null && (list == last && list._edges != null)
          || (list == null && last != null)) {
        ++emptiedDlists;
        DagNode d = new DagNode(FSGrammar.TOP_TYPE);
        newCopy._edges = new ArrayList<DagEdge>(2);
        newCopy._edges.add(new DagEdge(fsgrammar.listFeatureId, d));
        newCopy._edges.add(new DagEdge(fsgrammar.lastFeatureId, d));
      }
      */
    } else {
      in.setCopy(INSIDE);

      int newsize = 0;
      int cursorArcs = -1, cursorCompArcs = -1;
      if (in._edges != null) {
        cursorArcs = 0;
        newsize = in._edges.size();
      }
      if (_generation == currentGeneration && in._compArcs != null) {
        cursorCompArcs = 0;
        newsize += in._compArcs.size();
      }

      if (cursorArcs != -1 || cursorCompArcs != -1) {
        newCopy._edges = new ArrayList<DagEdge>(newsize);
      }
      DagRestrictor.Iterator it = m.iterator();
      while (cursorArcs != -1 || cursorCompArcs != -1) {
        DagEdge arc = null ;
        if (cursorArcs != -1 &&
            (cursorCompArcs == -1
            || (in._compArcs.get(cursorCompArcs).feature
                > in._edges.get(cursorArcs).feature))) {
          int curr = cursorArcs;
          if (++cursorArcs == in._edges.size()) {
            cursorArcs = -1;
          }
          arc = in._edges.get(curr);
        } else {
          int curr = cursorCompArcs;
          if (++cursorCompArcs == in._compArcs.size()) {
            cursorCompArcs = -1;
          }
          arc = in._compArcs.get(curr);
        }

        short feat = arc.feature;
        DagRestrictor sub = it.next(feat);

        if (m == null || m.keep(feat, sub)) {
          DagNode child = arc.value.copyResultRec(sub);
          if (true || ! (child._edges == null
                 && newType == fsgrammar.getAppropriateType(feat)
                 && child.getType() == fsgrammar.getMaxAppropriateType(feat))){
            newCopy._edges.add(new DagEdge(feat, child));
          }
        }
      }
      newCopy.edgesAreEmpty();
    }

    in.setCopy(newCopy);
    in._compArcs = null;
    // if resetting the copy slot is really necessary, it must be done AFTER
    // copying has finished in a new recursive walkthrough
    //in.setCopy(null);
    return newCopy;
  }

  /** Copy the result after a series of unifications.
  *
  *  This does *NOT* implement partial copying, so the resulting dag will be
  *  completely independent of the unified source structures, which makes it
  *  safe to use them in a parallel execution environment, as long as it's not
  *  during unification
  *
  * @param deleteDaughters delete some top level features only concerned with
  *                        building the constituent tree (grammar specified)
  * @return a copied result independent from the input dag
  */
  public DagNode copyResult(DagRestrictor restrictor) {
    // Return a copied result using the scratch buffer of this node
    DagNode result;
    try {
      result = copyResultRec(restrictor);
    } catch (CycleError err) {
      result = null;
    }
    invalidate();
    return result;
  }

  /** Copy the result after a series of unifications.
   *
   *  This does *NOT* implement partial copying, so the resulting dag will be
   *  completely independent of the unified source structures, which makes it
   *  safe to use them in a parallel execution environment, as long as it's not
   *  during unification
   *
   * @param deleteDaughters delete some top level features only concerned with
   *                        building the constituent tree (grammar specified)
   * @return a copied result independent from the input dag
   */
  public DagNode copyResult(DagNode restrictor) {
    // Return a copied result using the scratch buffer of this node
    DagNode result = copyResultRec(restrictor, null);
    invalidate();
    return result;
  }

  /** Copy the result after a series of unifications.
  *
  *  This does *NOT* implement partial copying, so the resulting dag will be
  *  completely independent of the unified source structures, which makes it
  *  safe to use them in a parallel execution environment, as long as it's not
  *  during unification
  *
  * @param restrictor a dag node representing a restrictor
  * @param toDelete if a feature is in this set, it is to be deleted
  * @return a copied result independent from the input dag
  *
 public DagNode copyResult(DagNode restrictor, TShortHashSet toDelete) {
   // Return a copied result using the scratch buffer of this node
   DagNode result = copyResultRec(restrictor, toDelete);
   invalidate();
   return result;
 }
 */

  private boolean makeWellformed(int unifiedType) {
    long generationSave = currentGeneration;
    currentGeneration = ++currentGenerationMax;
    // need a new generation to make a fresh copy: special invalidation
    DagNode typeDag = fsgrammar.getFS(unifiedType).dag();
    // don't call the normal invalidation here
    typeDag = typeDag.cloneFSRec();
    currentGeneration = generationSave;
    if (typeDag._edges != null) {
      return unifyFS1(typeDag, null);
    }
    return true;
  }

  @SuppressWarnings("null")
  private boolean unifyFS1(DagNode arg, IntTrie<int[]> _curr) {
    DagNode in1 = this.dereference();
    DagNode in2 = arg.dereference();
    if (in1.getCopy() == INSIDE) {
      if (recordFailures)
        forwardFailures.put(this, FailType.CYCLE);
      return false;
    }

    if (in1 == in2) return true;

    int type1 = in1.getNewType();
    int type2 = in2.getNewType();

    int unifType = fsgrammar.unifyTypes(type1, type2);
    if (unifType == FSGrammar.BOTTOM_TYPE) {
      if (_curr != null) {
        int[] f = _curr.getValue();
        if (f == null)
          f = new int[1];
        f[0]++;
        _curr.setValue(f);
      }

      if (recordFailures)
        forwardFailures.put(this, FailType.TYPE);
      return false;
    }

    in1.setNewType(unifType); // this makes all scratch slots of in1 current
    // when will nothing happen in wff unification (according to pet)
    // a) if the new type is the same as both old types
    // b) if the edge lists of both nodes are empty (including compArcs)
    // c) if the one that changed type has no edges (including compArcs)
    //    if ((type1 == unifType && type2 == unifType) ||
    //        (in1.newEdgesAreEmpty() && in2.newEdgesAreEmpty()) ||
    //        (type1 != unifType && in1.newEdgesAreEmpty()) ||
    //        (type2 != unifType && in2.newEdgesAreEmpty())) {
    // i was more picky, but that resulted in extreme performance degradation
    // if the type has changed, the edge lists of both must be empty
    if ((type1 == unifType && type2 == unifType)
        || (in1.newEdgesAreEmpty() && in2.newEdgesAreEmpty())
        || (type1 == unifType && ! in1.newEdgesAreEmpty())
        || (type2 == unifType && ! in2.newEdgesAreEmpty())) {
    } else {
      if (! in1.makeWellformed(unifType)) {
        if (recordFailures)
          forwardFailures.put(this, FailType.WELLFORMED);
        return false;
      }
      in1 = in1.dereference();
    }

    EdgeIterator arc1It = in1.getNewEdgeIterator();
    EdgeIterator arc2It = in2.getNewEdgeIterator();

    // the test if the iterators are null is not necessary here (can't occur
    // with a call to getNewEdgeIterator)
    DagEdge arc1 = null, arc2 = null;
    short feat1 = ((arc1It != null && arc1It.hasNext())
                   ? (arc1 = arc1It.next()).feature : NO_FEAT);
    short feat2 = ((arc2It != null && arc2It.hasNext())
                   ? (arc2 = arc2It.next()).feature : NO_FEAT);

    if (feat2 == NO_FEAT) {
      in2.setForward(in1);  // this makes all scratch slots of in2 current
    } else if (feat1 == NO_FEAT) {
      in2.setNewType(unifType); // this makes all scratch slots of in1 current
      in1.setForward(in2);
    } else {
      in1.setCopy(INSIDE);
      in2.setForward(in1);

      while (feat1 != NO_FEAT || feat2 != NO_FEAT) {
        while (feat1 < feat2) {
          // feature in 1 but not in 2: skip
          feat1 = (arc1It.hasNext() ? (arc1 = arc1It.next()).feature : NO_FEAT);
        }
        while (feat1 > feat2) { // feature in 2 missing in 1: add to compArcs
          arc1It.add(arc2);
          feat2 = (arc2It.hasNext() ? (arc2 = arc2It.next()).feature : NO_FEAT);
        }
        if (feat1 == feat2 && feat1 != NO_FEAT) {
          if (! arc1.value.unifyFS1(arc2.value,
              _curr == null ? _curr : _curr.add(feat1)))
            return false;
          feat1 = (arc1It.hasNext() ? (arc1 = arc1It.next()).feature : NO_FEAT);
          feat2 = (arc2It.hasNext() ? (arc2 = arc2It.next()).feature : NO_FEAT);
        }
      }
      in1.setCopy(null);
    }

    return true;
  }

  /** Unify the \c this feature structure with \p arg and return a copy of the
   *  result, if unification succeeds, \c null otherwise
   */
  public DagNode unifyFS(DagNode arg) {
    DagNode result = null;
    if (unifyFS1(arg, paths)) {
      try {
        result = copyResultRec();
      } catch (CycleError err) {
        result = null;
      }
    }
    invalidate();
    return result;
  }

  /** Unify \p arg with the subnode \p sub of \c this, and return a copy of the
   *  result, if unification succeeds, \c null otherwise.
   */
  public DagNode unifyFS(DagNode arg, DagNode sub) {
    if (sub == null) return null;
    DagNode result = null;
    if (sub.unifyFS1(arg, paths)) {
      try {
        result = copyResultRec();
      } catch (CycleError err) {
        result = null;
      }
    }
    invalidate();
    return result;
  }

  /** Unify \p arg into the \p argNo'th argument position of \c this
   *  and return a copy of the result, if unification succeeds,
   *  \c null otherwise. This assumes that \c this contains a list under
   *  DagNode.ARGS_FEATURE, and \c argNo then specifies the path where
   *  the unification will take place.
   */
  public DagNode unifyFS(DagNode arg, int argNo) {
    DagNode subNode = this.getNthArg(argNo);
    return unifyFS(arg, subNode);
  }

  /** Unify \p arg into the \p argNo'th argument position of \c this
   *  and return the result, if unification succeeds,
   *  \c null otherwise. In contrast to @see unifyFS, this does not copy the
   *  result and is intended for cases where multiple unifications are done
   *  before the final copy is made.
   */
  public boolean unifyOnly(DagNode arg, int argNo) {
    DagNode subnode = this.getNthArg(argNo);
    return (subnode != null && subnode.unifyFS1(arg, paths));
  }

  /** Unify \p arg with \c this and return the result, if unification succeeds,
   *  \c null otherwise. In contrast to @see unifyFS, this does not copy the
   *  result and is intended for cases where multiple unifications are done
   *  before the final copy is made.
   */
  public DagNode unifyOnly(DagNode arg) {
    return (unifyFS1(arg, paths) ? this : null);
  }

  /** Test the unifiability of \c this and \p arg.
   *  @attention This method will NOT report all unification failures because
   *  not all cyclic feature structures can be found during unification itself
   *  and there is no explicit cycle check done after the non-permanent
   *  unification.
   */
  public boolean isUnifiable(DagNode arg) {
    boolean result = unifyFS1(arg, paths);
    invalidate();
    return result;
  }


  private boolean checkCyclesRec() {
    if (visited() < 0) {
      setVisited(0);
      setCopy(INSIDE);
      for(EdgeIterator edgeIt = new EdgeIterator(); edgeIt.hasNext();) {
        DagEdge fvpair = edgeIt.next();
        if (fvpair.getValue().checkCyclesRec()) return true;
      }
      setCopy(null);
    } else {
      if (visited() == 0) {
        if (getCopy() == INSIDE) return true;
        setVisited(1);
      }
    }
    return false;
  }

  public boolean checkCycles() {
    boolean result = checkCyclesRec();
    invalidate();
    return result;
  }

  private int countCorefsRec(int maxCoref) {
    if (visited() < 0) {
      setVisited(0);
      for(EdgeIterator edgeIt = new EdgeIterator(); edgeIt.hasNext();) {
        DagEdge fvpair = edgeIt.next();
        maxCoref = fvpair.getValue().countCorefsRec(maxCoref);
      }
    } else {
      if (visited() == 0) {
        setVisited(++maxCoref);
      }
    }
    return maxCoref;
  }

  public int countCorefs() {
    int result = countCorefsRec(0);
    invalidate();
    return result;
  }

  private int countCorefsRigidRec(int maxCoref) {
    if (visited() <= 0) {
      if (visited() < 0) {
        setVisited(0);
      }
      else {
        setVisited(++maxCoref);
      }
      for(EdgeIterator edgeIt = new EdgeIterator(); edgeIt.hasNext();) {
        DagEdge fvpair = edgeIt.next();
        maxCoref = fvpair.getValue().countCorefsRigidRec(maxCoref);
      }
    }
    return maxCoref;
  }

  /** This differs from countCoref in that subnodes of coreferenced nodes will
   *  also be tagged with coreferences, not just the topmost reentrancy
   */
  public int countCorefsRigid() {
    int result = countCorefsRigidRec(0);
    return result;
  }

  private int countCorefsRigidRecSafe(IdentityHashMap<DagNode, Integer> result,
      int maxCoref){
    if (! result.containsKey(this)) {
      result.put(this, 0);
    } else {
      if (result.get(this) > 0) {
        // already visited twice, stop recursion
        return maxCoref;
      }
      // result.get(this) == 0
      result.put(this, ++maxCoref);
    }
    for(EdgeIterator edgeIt = new EdgeIterator(); edgeIt.hasNext();) {
      DagEdge fvpair = edgeIt.next();
      maxCoref = fvpair.getValue().countCorefsRigidRecSafe(result, maxCoref);
    }
    return maxCoref;
  }

  /** This differs from countCoref in that subnodes of coreferenced nodes will
   *  also be tagged with coreferences, not just the topmost reentrancy
   */
  public int countCorefsRigidSafe(IdentityHashMap<DagNode, Integer> result) {
    return countCorefsRigidRecSafe(result, 0);
  }

  @SuppressWarnings("null")
  private int subsumesBiRec(DagNode in2, int result) {
    { DagNode fs1 = this.getForward();
      if ((result & THIS_MORE_GENERAL) != 0) {
        if (fs1 == null) {
          this.setForward(in2);
        } else {
          if (fs1 != in2) { // forward = false
            if (recordFailures)
              forwardFailures.put(this, FailType.VARIABLE);
            if ((result &= THIS_MORE_GENERAL_MASK) == 0) return 0;
          } else {
            return result;
          }
        }
      }
    }
    { DagNode fs2 = in2.getCopy();
      if ((result & ARG_MORE_GENERAL) != 0) {
        if (fs2 == null) {
          in2.setCopy(this);
        } else {
          if (fs2 != this) {  // backward = false
            if (recordFailures)
              backwardFailures.put(this, FailType.VARIABLE);
            if ((result &= ARG_MORE_GENERAL_MASK) == 0) return 0;
          } else {
            return result;
          }
        }
      }
    }
    int type1 = this.getNewType();
    int type2 = in2.getNewType();
    if (type1 != type2) {
      if (! fsgrammar.subsumesType(type1, type2)) {
        if (recordFailures)
          forwardFailures.put(this, FailType.TYPE);
        if ((result &= THIS_MORE_GENERAL_MASK) == 0) return 0;
      }
      if (! fsgrammar.subsumesType(type2, type1)) {
        if (recordFailures)
          backwardFailures.put(this, FailType.TYPE);
        if ((result &= ARG_MORE_GENERAL_MASK) == 0) return 0;
      }
    }

    List<DagEdge> edges1 = this.getEdges();
    List<DagEdge> edges2 = in2.getEdges();
    if (edges1 == null || edges2 == null) {
      if (edges1 != edges2) {
        if (edges1 == null) {
          if (recordFailures)
            backwardFailures.put(this, FailType.FEATURE);
          if ((result &= ARG_MORE_GENERAL_MASK) == 0) return 0;
        } else {
          if (recordFailures)
            forwardFailures.put(this, FailType.FEATURE);
          if ((result &= THIS_MORE_GENERAL_MASK) == 0) return 0;
        }
      }
      return result;
    }

    Iterator<DagEdge> arc1It = edges1.iterator();
    Iterator<DagEdge> arc2It = edges2.iterator();
    DagEdge arc1 = null, arc2 = null;
    int feat1 = (arc1It.hasNext() ? (arc1 = arc1It.next()).feature : NO_FEAT);
    int feat2 = (arc2It.hasNext() ? (arc2 = arc2It.next()).feature : NO_FEAT);
    while (feat1 != NO_FEAT && feat2 != NO_FEAT) {
      if (feat1 < feat2) { // feature in 1 missing in 2: no forward
        if (recordFailures)
          forwardFailures.put(this, FailType.FEATURE);
        if ((result &= THIS_MORE_GENERAL_MASK) == 0) return 0;
        while (feat1 < feat2) {
          feat1 = (arc1It.hasNext() ? (arc1 = arc1It.next()).feature : NO_FEAT);
        }
      }
      if (feat1 > feat2) { // feature in 2 missing in 1: no backward
        if (recordFailures)
          backwardFailures.put(this, FailType.FEATURE);
        if ((result &= ARG_MORE_GENERAL_MASK) == 0) return 0;
        while (feat1 > feat2) {
          feat2 = (arc2It.hasNext() ? (arc2 = arc2It.next()).feature : NO_FEAT);
        }
      }
      if (feat1 == feat2 && feat1 != NO_FEAT) {
        if ((result = arc1.value.subsumesBiRec(arc2.value, result)) == 0)
          return 0;
        feat1 = (arc1It.hasNext() ? (arc1 = arc1It.next()).feature : NO_FEAT);
        feat2 = (arc2It.hasNext() ? (arc2 = arc2It.next()).feature : NO_FEAT);
      }
    }
    if (feat1 != feat2) {
      if (feat1 == NO_FEAT) { // more features in arg: this is more general
        if (recordFailures)
          backwardFailures.put(this, FailType.FEATURE);
        result &= ARG_MORE_GENERAL_MASK;
      } else {
        if (recordFailures)
          forwardFailures.put(this, FailType.FEATURE);
        result &= THIS_MORE_GENERAL_MASK;
      }
    }

    return result;
  }

  /** compute the subsumption relation between this and fs in both directions:
   * FORWARD subsumption means that `this' subsumes (is a more general)
   * structure than `fs', while
   * BACKWARD subsumption means that `this' is subsumed by (more informative
   * than) `fs'
   */
  public int subsumesBi(DagNode fs) {
    if (recordFailures) {
      forwardFailures.clear();
      backwardFailures.clear();
    }
    int result = subsumesBiRec(fs, THIS_MORE_GENERAL + ARG_MORE_GENERAL);
    invalidate();
    return result;
  }

  @SuppressWarnings("null")
  private boolean subsumesRec(DagNode in2) {
    { DagNode fs1 = this.getForward();
      if (fs1 == null) {
        this.setForward(in2);
      } else {
        return (fs1 == in2);
      }
    }

    int type1 = this.getNewType();
    int type2 = in2.getNewType();
    if (type1 != type2) {
      if (! fsgrammar.subsumesType(type1, type2)) {
        return false;
      }
    }

    List<DagEdge> edges1 = this.getEdges();
    List<DagEdge> edges2 = in2.getEdges();
    if (edges2 == null) {
      return (edges1 == edges2);
    }
    if (edges1 == null) {
      return true;
    }

    Iterator<DagEdge> arc1It = edges1.iterator();
    Iterator<DagEdge> arc2It = edges2.iterator();
    DagEdge arc1 = null, arc2 = null;
    int feat1 = (arc1It.hasNext() ? (arc1 = arc1It.next()).feature : NO_FEAT);
    int feat2 = (arc2It.hasNext() ? (arc2 = arc2It.next()).feature : NO_FEAT);
    while (feat1 != NO_FEAT && feat2 != NO_FEAT) {
      if (feat1 < feat2) { // feature in 1 missing in 2: no forward
        return false;
      }
      if (feat1 > feat2) { // feature in 2 missing in 1: no backward
        while (feat1 > feat2) {
          feat2 = (arc2It.hasNext() ? (arc2 = arc2It.next()).feature : NO_FEAT);
        }
      }
      if (feat1 == feat2 && feat1 != NO_FEAT) {
        if (! arc1.value.subsumesRec(arc2.value)) return false;
        feat1 = (arc1It.hasNext() ? (arc1 = arc1It.next()).feature : NO_FEAT);
        feat2 = (arc2It.hasNext() ? (arc2 = arc2It.next()).feature : NO_FEAT);
      }
    }
    return ((feat1 == feat2) || (feat1 == NO_FEAT));
  }

  /** Return true if `this' is more general than fs */
  public boolean subsumes(DagNode fs) {
    boolean result = subsumesRec(fs);
    invalidate();
    return result;
  }


  /** return true if fs is more general than `this' */
  public boolean isSubsumedBy(DagNode fs) {
    boolean result = (fs).subsumesRec(this);
    invalidate();
    return result;
  }

  @SuppressWarnings("null")
  private boolean equalsRec(DagNode in2) {
    DagNode fs1 = getForward();
    DagNode fs2 = in2.getForward();
    if (fs1 == null && fs2 == null) {
      in2.setForward(this);
      this.setForward(this);
    } else {
      // check if already visited
      if (fs1 == fs2) return true;
    }

    if (fs1 != fs2) return false;

    int type1 = this.getType();
    int type2 = in2.getType();
    if (type1 != type2) {
      return false;
    }

    List<DagEdge> edges1 = this.getEdges();
    List<DagEdge> edges2 = in2.getEdges();
    if (edges1 == null || edges2 == null) {
      return (edges1 == edges2);
    }

    Iterator<DagEdge> arc1It = edges1.iterator();
    Iterator<DagEdge> arc2It = edges2.iterator();
    DagEdge arc1 = null, arc2 = null;
    int feat1 = (arc1It.hasNext() ? (arc1 = arc1It.next()).feature : NO_FEAT);
    int feat2 = (arc2It.hasNext() ? (arc2 = arc2It.next()).feature : NO_FEAT);
    while (feat1 == feat2 &&  feat1 != NO_FEAT) {
      if (! arc1.value.equalsRec(arc2.value))
        return false;
      feat1 = (arc1It.hasNext() ? (arc1 = arc1It.next()).feature : NO_FEAT);
      feat2 = (arc2It.hasNext() ? (arc2 = arc2It.next()).feature : NO_FEAT);
    }
    return (feat1 == feat2);
  }

  @Override
  public boolean equals(Object obj) {
    if (! (obj instanceof DagNode)) return false;
    boolean result = equalsRec((DagNode) obj);
    invalidate();
    return result;
  }

  /** Add an edge array of the right size */
  public void addEdges(int noArcs) {
    _edges = new ArrayList<DagEdge>(noArcs);
  }

  /** We assume the feature list is either equal to null or not empty. Other
   *  code can rely on that
   */
  private void addEdge(DagEdge undumpArc) {
    if (null == _edges) _edges = new ArrayList<DagEdge>(3);
    _edges.add(undumpArc);
  }

  public void addEdge(short featCode, DagNode fs) {
    addEdge(new DagEdge(featCode, fs));
  }

  private ArrayList<DagEdge> getEdges() {
    return _edges;
  }

  /** This edge iterator works correctly only on complete dags.
   *  It should be preferred if it can be made sure that the dag is complete.
   */
  public Iterator<DagEdge> getEdgeIterator() {
    return _edges == null ? emptyEdges : _edges.iterator();
  }

  /** This edge iterator works correctly both on complete and temporary dags.
   *  Using it extensively is therefore much more expensive, and should be
   *  avoided if it can be made sure that the dag is complete
   */
  public EdgeIterator getTransitionalEdgeIterator() {
    return new EdgeIterator();
  }

  /** Return the substructure under feature, if existent, null otherwise
   * Could be improved using binary or interpolation search.
   * Works correctly only on non-temporary dags.
   */
  public DagNode getValue(short feature) {
    DagEdge edge = getEdge(feature);
    return (edge == null) ? null : edge.getValue();
  }

  /** Return the edge leaving this dag labeled with feature, if existent,
   *  null otherwise
   * Could be improved using binary or interpolation search.
   * Works correctly only on non-temporary dags.
   */
  public DagEdge getEdge(short feature) {
    if (_edges == null) return null;
    for (DagEdge edge : _edges) {
      int f = edge.getFeature();
      if (f == feature)
        return edge;
      if (f > feature)
        break;
    }
    return null;
  }

  private void sortEdges() {
    if (_edges != null)
      Collections.sort(_edges);
  }

  // clear the edges slot if it is not needed
  protected void edgesAreEmpty() {
    if (_edges != null && _edges.size() == 0) _edges = null;
  }

  // **************************************************************************
  // BEGIN general convenience functions, path/arg access, etc.
  // **************************************************************************

  private int
  countCorefsLocal(IdentityHashMap<DagNode, Integer> corefs, int nextCorefNo) {
    DagNode here = dereference();
    Integer corefNo = corefs.get(here);
    if (corefNo == null) { // visited for the first time
      corefs.put(here, 0);
      EdgeIterator fvListIt = here.getNewEdgeIterator();
      if (fvListIt != null) {
        while(fvListIt.hasNext()) {
          nextCorefNo = fvListIt.next().getValue()
            .countCorefsLocal(corefs, nextCorefNo);
        }
      }
    } else {
      if (corefNo == 0) { // visited for the second time at least
        corefs.put(here, ++nextCorefNo);
      }
    }
    return nextCorefNo;
  }

  public int getListLength() {
    int result = 0;
    DagNode curr = this;
    while ((curr = curr.getValue(fsgrammar.restFeatureId)) != null) {
      ++result;
    }
    return result;
  }

  public int getArity() {
    DagNode args = getValue(fsgrammar.argsFeatureId);
    if (args == null) return 0;
    return args.getListLength();
  }

  public DagNode getNthArg(int argNo) {
    DagNode subnode = getValue(ARGS_FEATURE);
    while (argNo != 0 && subnode != null) {
      subnode = subnode.getValue(REST_FEATURE);
      --argNo;
    }
    return (subnode == null ? null : subnode.getValue(FIRST_FEATURE));
  }

  /** Get the node under the given path.
   *  Works correctly only on non-temporary dags.
   */
  public DagNode getSubNode(Iterator<Short> path) {
    DagNode current = this;
    while (path.hasNext() && current != null) {
      current = current.getValue(path.next());
    }
    return current;
  }

  /** Return the key arg of this structure, or -1 if there is none */
  public int getKeyArg() {
    int result = -1;
    DagNode curr = getValue(fsgrammar.argsFeatureId);
    int arg = 0;
    while (curr != null && result == -1) {
      DagNode key = curr.getValue(fsgrammar.firstFeatureId);
      if (key != null) {
        key = key.getSubNode(fsgrammar.keyargMarkerPath.iterator());
      }
      if (key != null && key.getType() == fsgrammar.trueTypeId) {
        result = arg;
      } else {
        ++arg;
        curr = curr.getValue(fsgrammar.restFeatureId);
      }
    }
    return result;
  }


  /** Remove the edge with the given feature. Works correctly only on
   * non-temporary dags.
   */
  public void removeEdge(short feature) {
    Iterator<? extends DagEdge> it = getEdgeIterator();
    if (it == null) return ;
    while (it.hasNext()) {
      DagEdge edge = it.next();
      if (edge.getFeature() == feature) {
        it.remove();
        return;
      }
    }
  }

  public void deleteDaughters() {
    Iterator<? extends DagEdge> it = getEdgeIterator();
    if (it == null) return ;
    while (it.hasNext()) {
      DagEdge edge = it.next();
      if (! fsgrammar.keepFeature(edge.getFeature())) {
        it.remove();
      }
    }
    edgesAreEmpty();
  }

  // *************************************************************************
  // Begin Restrictor and Error Case Reduction
  // *************************************************************************

  RESTRICT getRestrictorType() {
    return RESTRICT.values()[getType()];
  }

  public void transformRestrictorRec(IdentityHashMap<DagNode, DagNode>visited){
    DagNode here = dereference();
    if (visited.containsKey(here)) return;
    visited.put(here, here);
    int value = here.getType();
    if (value != FSGrammar.TOP_TYPE) {
      String valString = fsgrammar.getTypeName(value);
      // could also be a string constant
      if (valString.startsWith("\""))
        valString = valString.substring(1, valString.length() - 1);
      int commaPos = 0;
      // ignore type generalizations of new version restrictors
      if ((commaPos = valString.indexOf(',')) > 0)
        valString = valString.substring(0, commaPos);
      value = RESTRICT.valueOf(valString.toUpperCase()).ordinal();
    }
    here.setType(value);
    Iterator<? extends DagEdge> arc1It = here.getEdgeIterator();
    if (arc1It != null) {
      while (arc1It.hasNext()) {
        arc1It.next().getValue().transformRestrictorRec(visited);
      }
    }
  }

  public void transformRestrictorDag() {
    transformRestrictorRec(new IdentityHashMap<DagNode, DagNode>());
  }

  @SuppressWarnings("null")
  private void restrictRec(DagNode restrictor) {
    if (this.getCopy() == restrictor) return;
    this.setCopy(restrictor);
    RESTRICT restrictType = restrictor.getRestrictorType();

    Iterator<? extends DagEdge> arc1It = this.getEdgeIterator();
    Iterator<? extends DagEdge> arc2It = restrictor.getEdgeIterator();
    DagEdge arc1 = null, arc2 = null;
    short feat1 = ((arc1It != null && arc1It.hasNext())
                   ? (arc1 = arc1It.next()).getFeature() : NO_FEAT);
    short feat2 = ((arc2It != null && arc2It.hasNext())
                   ? (arc2 = arc2It.next()).getFeature() : NO_FEAT);

    // NO plus no outgoing restrictor edges: there will be no restriction here
    if (restrictType == RESTRICT.RSTR_NO && feat2 == NO_FEAT) return;

    while (feat1 != NO_FEAT || feat2 != NO_FEAT) {
      while (feat1 < feat2) {
        // feature in this dag but not in restrictor
        if (restrictType == RESTRICT.RSTR_KEEP) {
          arc1It.remove(); // delete the not mentioned feature
        }
        feat1 = (arc1It.hasNext()
                 ? (arc1 = arc1It.next()).getFeature() : NO_FEAT);
      }
      while (feat1 > feat2) { // feature in restrictor missing in this dag
        feat2 = (arc2It.hasNext()
                 ? (arc2 = arc2It.next()).getFeature() : NO_FEAT);
      }
      if (feat1 == feat2 && feat1 != NO_FEAT) {
        if (arc2.getValue().getRestrictorType() == RESTRICT.RSTR_DEL) {
          arc1It.remove();
        } else {
          arc1.getValue().restrictRec(arc2.getValue());
        }
        feat1 = (arc1It.hasNext()
                 ? (arc1 = arc1It.next()).getFeature() : NO_FEAT);
        feat2 = (arc2It.hasNext()
                 ? (arc2 = arc2It.next()).getFeature() : NO_FEAT);
      }
    }
    edgesAreEmpty();
  }

  /** Recursively restrict a dag using a given restrictor dag
   *  The restrictor dag is a "pseudo dag", i.e., the types have special
   *  meanings.
   */
  public void restrict(DagNode restrictor) {
    restrictRec(restrictor);
    invalidate();
  }

  public static int emptiedDlists = 0;
  public static int depthRestrictedSlashes = 0;

  @SuppressWarnings("null")
  private void restrictSpecialRec(DagNode restrictor, boolean sloppy,
      int slashDepth) {
    if (this.getCopy() == restrictor) return;
    this.setCopy(restrictor);

    /**/
    // first check if this is an empty DLIST that should be massaged
    if (fsgrammar.subsumesType(fsgrammar.dListTypeId, getType())) {
      DagNode list = getValue(fsgrammar.listFeatureId);
      if (list != null) {
        DagNode last = getValue(fsgrammar.lastFeatureId);
        if (list == last && list._edges != null) {
          ++emptiedDlists;
          list._edges = null;
          list._compArcs = null;
          last._edges = null;
          last._compArcs = null;
          // list._typeCode = fsgrammar.nullTypeId; // this is illegal!
        }
      }
    }
    /**/

    RESTRICT restrictType = restrictor.getRestrictorType();

    Iterator<? extends DagEdge> arc1It = this.getEdgeIterator();
    Iterator<? extends DagEdge> arc2It = restrictor.getEdgeIterator();
    DagEdge arc1 = null, arc2 = null;
    short feat1 = ((arc1It != null && arc1It.hasNext())
                   ? (arc1 = arc1It.next()).getFeature() : NO_FEAT);
    short feat2 = ((arc2It != null && arc2It.hasNext())
                   ? (arc2 = arc2It.next()).getFeature() : NO_FEAT);

    // NO plus no outgoing restrictor edges: there will be no restriction here
    if (restrictType == RESTRICT.RSTR_NO && feat2 == NO_FEAT) return;

    while (feat1 != NO_FEAT || feat2 != NO_FEAT) {
      while (feat1 < feat2) {
        // feature in this dag but not in restrictor
        if (restrictType == RESTRICT.RSTR_KEEP) {
          arc1It.remove(); // delete the not mentioned feature
        } else {
          DagNode dag = arc1.getValue();
          //dag.unfillRec(sloppy);
          if ((dag._edges == null || dag._edges.isEmpty())
              && (sloppy || getType() == fsgrammar.getAppropriateType(arc1.getFeature()))
              && dag.getType() == fsgrammar.getMaxAppropriateType(arc1.getFeature())) {
            arc1It.remove();
          }
        }
        feat1 = (arc1It.hasNext()
                 ? (arc1 = arc1It.next()).getFeature() : NO_FEAT);
      }
      while (feat1 > feat2) { // feature in restrictor missing in this dag
        feat2 = (arc2It.hasNext()
                 ? (arc2 = arc2It.next()).getFeature() : NO_FEAT);
      }
      if (feat1 == feat2 && feat1 != NO_FEAT) {
        if (arc2.getValue().getRestrictorType() == RESTRICT.RSTR_DEL) {
          arc1It.remove();
        } else {
          DagNode dag = arc1.getValue();
          // this increases slashDepth if arc1 is SLASH arc
          if (feat1 == SLASH_FEATURE && (++slashDepth == MAX_SLASH_DEPTH)) {
            // max slash depth exceeded
            // dag is the slash dlist, make it an empty dlist
            DagNode list = dag.getValue(fsgrammar.listFeatureId);
            if (list != null) {
              ++depthRestrictedSlashes;
              list._edges = null;
              list._compArcs = null;
              // list._typeCode = fsgrammar.nullTypeId; // this is illegal!
              DagEdge lastEdge = dag.getEdge(fsgrammar.lastFeatureId);
              lastEdge.value = list;
            }
          } else {
            dag.restrictSpecialRec(arc2.getValue(), sloppy, slashDepth);
            if ((dag._edges == null || dag._edges.isEmpty())
                && (sloppy || getType() == fsgrammar.getAppropriateType(arc1.getFeature()))
                && dag.getType() == fsgrammar.getMaxAppropriateType(arc1.getFeature())) {
              arc1It.remove();
            }
          }
        }
        feat1 = (arc1It.hasNext()
                 ? (arc1 = arc1It.next()).getFeature() : NO_FEAT);
        feat2 = (arc2It.hasNext()
                 ? (arc2 = arc2It.next()).getFeature() : NO_FEAT);
      }
    }

    edgesAreEmpty();
  }

  /** Recursively restrict a dag using a given restrictor dag
   *  The restrictor dag is a "pseudo dag", i.e., the types have special
   *  meanings.
   *
   *  Additionally, this restriction method deletes remaining edges in empty
   *  dlists, it deletes slash embeddings of a depth greater than
   *  MAX_SLASH_DEPTH and unfills.
   */
  public void restrictSpecial(DagNode restrictor) {
    restrictSpecialRec(restrictor, false, 0);
    invalidate();
  }

  @SuppressWarnings("null")
  public void getQCVector(DagNode qcnode, DagNode[] qcvector) {
    int qcPos = qcnode.getType();
    if (qcPos > 0 && qcPos <= qcvector.length) {
      qcvector[qcPos - 1] = this;
    }

    Iterator<? extends DagEdge> arc1It = this.getEdgeIterator();
    Iterator<? extends DagEdge> arc2It = qcnode.getEdgeIterator();
    DagEdge arc1 = null, arc2 = null;
    short feat1 = ((arc1It != null && arc1It.hasNext())
                   ? (arc1 = arc1It.next()).getFeature() : NO_FEAT);
    short feat2 = ((arc2It != null && arc2It.hasNext())
                   ? (arc2 = arc2It.next()).getFeature() : NO_FEAT);

    while (feat1 != NO_FEAT && feat2 != NO_FEAT) {
      while (feat1 < feat2) {
        // feature in this dag but not in qcnode
        feat1 = (arc1It.hasNext()
                 ? (arc1 = arc1It.next()).getFeature() : NO_FEAT);
      }
      while (feat1 > feat2) { // feature in qc vector missing in this dag
        feat2 = (arc2It.hasNext()
                 ? (arc2 = arc2It.next()).getFeature() : NO_FEAT);
      }
      if (feat1 == feat2 && feat1 != NO_FEAT) {
        arc1.getValue().getQCVector(arc2.getValue(), qcvector);

        feat1 = (arc1It.hasNext()
                 ? (arc1 = arc1It.next()).getFeature() : NO_FEAT);
        feat2 = (arc2It.hasNext()
                 ? (arc2 = arc2It.next()).getFeature() : NO_FEAT);
      }
    }
  }


  private void restrictSimpleRec(IdentityHashMap<DagNode, DagNode> visited) {
    Iterator<? extends DagEdge> arcIt = this.getEdgeIterator();
    if (visited.containsKey(this) || arcIt == null) return;
    visited.put(this, this);
    while (arcIt.hasNext()) {
      DagEdge arc = arcIt.next();
      if (! fsgrammar.keepFeature(arc.getFeature())) {
        arcIt.remove();
      } else {
        arc.getValue().restrictSimpleRec(visited);
      }
    }
    edgesAreEmpty();
  }

  public void restrict() {
    restrictSimpleRec(new IdentityHashMap<DagNode, DagNode>());
  }

  private void unfillRec(boolean sloppy) {
    Iterator<? extends DagEdge> arcIt = this.getEdgeIterator();
    if (visited() == 0)  // returns -1 if not visited
      return;

    setVisited(0);
    while (arcIt.hasNext()) {
      DagEdge arc = arcIt.next();
      DagNode dag = arc.getValue();
      dag.unfillRec(sloppy);
      if ((dag._edges == null || dag._edges.isEmpty())
          && (sloppy || getType() == fsgrammar.getAppropriateType(arc.getFeature()))
          && dag.getType() == fsgrammar.getMaxAppropriateType(arc.getFeature())) {
        arcIt.remove();
      }
    }
    edgesAreEmpty();
  }

  /** Remove all structures that can be explained by the maximally appropriate
   *  type for a structure and the appropriate type
   */
  public void unfill() {
    unfillRec(false);
    invalidate();
  }

  /** Remove all structures that can be explained by the maximally appropriate
   *  type for a structure
   */
  public void unfillSloppy() {
    unfillRec(true);
    invalidate();
  }

  private void unfillSimpleRec(IdentityHashMap<DagNode, DagNode> visited,
      boolean sloppy) {
    Iterator<? extends DagEdge> arcIt = this.getEdgeIterator();
    if (visited.containsKey(this) || arcIt == null) return;
    visited.put(this, this);
    while (arcIt.hasNext()) {
      DagEdge arc = arcIt.next();
      DagNode dag = arc.getValue();
      dag.unfillSimpleRec(visited, sloppy);
      if ((dag._edges == null || dag._edges.isEmpty())
          && (sloppy || getType() == fsgrammar.getAppropriateType(arc.getFeature()))
          && dag.getType() == fsgrammar.getMaxAppropriateType(arc.getFeature())) {
        arcIt.remove();
      }
    }
    edgesAreEmpty();
  }

  /** Remove all structures that can be explained by the maximally appropriate
   *  type for a structure and the appropriate type
   */
  public void unfillSafe() {
    unfillSimpleRec(new IdentityHashMap<DagNode, DagNode>(), false);
  }

  /** Remove all structures that can be explained by the maximally appropriate
   *  type for a structure
   */
  public void unfillSafeSloppy() {
    unfillSimpleRec(new IdentityHashMap<DagNode, DagNode>(), true);
  }

  public void reduceRec(ErrorProducer ep, DagNode resSubNode,
                        HashSet<DagNode> visited) {
    if (visited.contains(this)) return;
    visited.add(this);
    Iterator<? extends DagEdge> currentEdgeIt = this.getEdgeIterator();
    if (currentEdgeIt == null) return;
    // while (featureToRemove still available)
    while (currentEdgeIt.hasNext()) {
      // check error with enhanced restrictor (add featureToRemove)
      DagEdge currentEdge = currentEdgeIt.next();
      resSubNode.addEdge(currentEdge.getFeature(),
                         new DagNode(RESTRICT.RSTR_DEL.ordinal()));
      // if error persists, keep restrictor, otherwise remove last feature
      if (ep.errorPersists()) {
        // error is still there, proceed to the next feature
        // nothing to do here
      } else {
        // first remove current edge from restrictor
        resSubNode.removeEdge(currentEdge.getFeature());
        DagNode resSubNext =
          new DagNode(RESTRICT.RSTR_NO.ordinal());
        // try it one level deeper
        resSubNode.addEdge(currentEdge.getFeature(), resSubNext);
        currentEdge.getValue().reduceRec(ep, resSubNext, visited);
      }
      // get next featureToRemove
    }
  }

  private void walkDagRec(DagVisitor visitor,
      IdentityHashMap<DagNode, Integer> corefs) {
    DagNode here = this.dereference();
    int corefNo = corefs.get(here);
    visitor.startDag(this, here, corefNo);
    if (corefNo < 0) { // already visited
      return;
    }
    if (corefNo > 0) { // mark visited
      corefs.put(here, -corefNo);
    }

    EdgeIterator fvListIt = here.getNewEdgeIterator();
    if (fvListIt != null) {
      while(fvListIt.hasNext()) {
        DagEdge edge = fvListIt.next();
        visitor.visitEdge(here, edge);
        edge.getValue().walkDagRec(visitor, corefs);
      }
    }
    visitor.endDag(here);
  }

  public void walkDag(DagVisitor visitor) {
    IdentityHashMap<DagNode, Integer> corefMap =
        new IdentityHashMap<DagNode, Integer>();
    int corefs = 0;
    corefs = countCorefsLocal(corefMap, corefs);
    walkDagRec(visitor, corefMap);
  }

  // *************************************************************************
  // Begin construct jxchg string representation from (permanent) dag
  // *************************************************************************

  private class PrintVisitor implements DagVisitor {
    Writer sb;
    boolean readable;

    public PrintVisitor(Writer w, boolean read) {
      sb = w; readable = read;
    }

    @Override
    public void startDag(DagNode here, DagNode deref, int corefNo) {
      try {
        if (corefNo != 0) { // coref here
          sb.append(" #").append(Integer.toString(Math.abs(corefNo)))
            .append(' ');
        }
        if (corefNo >= 0) {
          sb.append('[').append(readable ? here.getTypeName()
                                         : Integer.toString(here.getType()));
        }
      }
      catch (IOException ioex) { throw new Error(ioex); }
    }

    @Override
    public void visitEdge(DagNode deref, DagEdge edge) {
      try {
        sb.append(' '); sb.append(readable ? edge.getName()
                                           : Short.toString(edge.getFeature()));
      }
      catch (IOException ioex) { throw new Error(ioex); }
    }

    @Override
    public void endDag(DagNode deref) {
      try { sb.append(']'); }
      catch (IOException ioex) { throw new Error(ioex); }
    }
  }

  public void write(Writer out) throws IOException {
    IdentityHashMap<DagNode, Integer> corefMap =
        new IdentityHashMap<DagNode, Integer>();
    int corefs = 0;
    corefs = countCorefsLocal(corefMap, corefs);
    if (_DEFAULT_PRINTER != null) {
      _DEFAULT_PRINTER.toStringRec(this, PRINT_READABLE, out, corefMap);
    }
    else {
      try { /** print fs in jxchg format */
        walkDagRec(new PrintVisitor(out, PRINT_READABLE), corefMap);
      } catch (Error e) {
        if (e.getCause() instanceof IOException)
          throw (IOException) e.getCause();
        else
          throw e;
      }
    }
  }

  @Override
  public String toString() {
    StringWriter sb = new StringWriter();
    try {
      write(sb);
    } catch (IOException e) { // Will never occur
      e.printStackTrace();
    }
    return sb.toString();
  }

  // *************************************************************************
  // Begin FS builders for different input formats
  // *************************************************************************

  /** return an atomic node containing only a type id and no features */
  public static DagNode buildFS(int typeID) {
    return new DagNode(typeID);
  }

  /** buildFS() produces the typed feature structure encoded in the stream in
   * PET binary format. The input is read from a stream wrapper of class
   * PetUndumper.
   *
   * The format that is recognized here is as follows:
   * <int noOfNodes> <int totalNoOfArcs>
   *  ( <int typeCode> <short noArcs>  ( <short feature> <nextNode> ) )[noNodes]
   *
   * @param u a stream wrapper of class PetUndumper
   * @return a TFS object
   */
  public static DagNode buildFS(PetUndumper u) {
    int noNodes = u.undumpInt();
    DagNode[] nodes = new DagNode[noNodes];
    // ... and fill the node array with empty feature structures in order to
    // avoid a missing feature structure, in case an arc refer to a node which
    // has not been created yet; tell the initial FS that this object is the
    // owner
    for (int j = 0; j < noNodes; j++) {
      nodes[j] = new DagNode(FSGrammar.BOTTOM_TYPE);
    }
    totalNoNodes = totalNoNodes + noNodes;
    // the next undumped int is uninteresting for us and tells us how many
    // arcs will be constructed for type identifier i
    totalNoArcs = totalNoArcs + u.undumpInt();
    // noNodes times read out a node
    for (int j = 0; j < noNodes; j++) {
      DagNode node = nodes[j];
      node.setType(u.undumpInt());
      // now read out the top-level arcs (feature-value pairs), i.e., pairs of
      // feature name identifiers and node ids which refer to a position in the
      // node array and add them
      short noArcs = u.undumpShort();
      if (noArcs > 0) {
        node.addEdges(noArcs); // node.edges = new ArrayList<DagEdge>(noArcs);
        for (short i = (short) 0; i < noArcs; i++) {
          short feature = u.undumpShort();
          short nodeIndex = u.undumpShort();
          node.addEdge(feature, nodes[nodeIndex]);
        }
        node.sortEdges();
      }
    }
    return nodes[nodes.length - 1];
  }


  /** buildFS1() does the recursive build-up for buildFS() from JxchgTokenizer
   * helper method for buildFS(JxchgTokenizer, FSGrammar)
   * @throws {@link IOException}, {@link InvalidSyntaxException}
   */
  private static DagNode
  buildFS1(JxchgTokenizer in, FSGrammar gram, ArrayList<DagNode> coref2FS,
      TFS container)
    throws IOException, InvalidSyntaxException {
    DagNode result = null;

    // if first token is not "[" or "#", something has gone wrong
    in.nextToken();
    if (in.ttype == '#') {
      // cases (2) and (3)
      Integer key = in.getNextInt();
      // has there already a fs been constructed for the coref?
      if (key < coref2FS.size()) {
        result = coref2FS.get(key);
      }
      if (result == null) {
        // establish coref-to-fs mapping, have to do it this way to allow for
        // cyclic dags
        result = new DagNode(FSGrammar.BOTTOM_TYPE);
        while (key >= coref2FS.size()) {
          coref2FS.add(null);
        }
        coref2FS.set(key, result);
        // case (3): <tfs> following the coref must be new, we've removed
        // the coref from the stream, so another call to buildFS1 will return
        // the plain new fs, put into the still empty this object
        DagNode placeHolder = buildFS1(in, gram, coref2FS, container);
        result._typeCode = placeHolder._typeCode;
        result._edges = placeHolder._edges;
      }
      // We're done
      return result;
    }

    if (in.ttype != '[')
      throw new InvalidSyntaxException("[", in);
    // next token must be a number, representing the type entry, or a string,
    // in which case it's a dynamic symbol from pet.
    in.nextToken();
    int iType = FSGrammar.BOTTOM_TYPE;
    if (in.ttype == StreamTokenizer.TT_NUMBER) {
      iType = in.getInt();
      if (! gram.isGrammarType(iType)) {
        System.out.println("Unknown type id "+ iType);
        // TODO PROPER HANDLING!
        iType = FSGrammar.TOP_TYPE;
      }
    } else {
      //int react = gram.getReaction();
      //gram.setReaction(0);
      iType = gram.getNumberForTypeName(in.sval);
      //gram.setReaction(react);
    }
    result = new DagNode(iType);

    // now read in the feature/value pairs until we find a "]"
    in.nextToken();
    while (in.ttype == StreamTokenizer.TT_NUMBER ||
           in.ttype == StreamTokenizer.TT_WORD) {
      // actual token must be a feature; now start the feature game ...
      short featval = FSGrammar.ILLEGAL_FEATURE;
      if (in.ttype == StreamTokenizer.TT_WORD) {
        featval = gram.getFeatureId(in.sval);
        if (featval == FSGrammar.ILLEGAL_FEATURE && UNKNOWN_FEATURE_ERROR) {
          throw new InvalidSyntaxException("Unknown Feature Name", in);
        }
      } else {
        featval = (short)in.nval;
      }
      if (gram.getNoOfFeatures() <= featval) {
        System.out.println("Unknown feature id "+ featval);
      }
      result.addEdge(featval, buildFS1(in, gram, coref2FS, container));
      in.nextToken();
    }
    in.checkToken(']');
    result.sortEdges();
    // found "]" and so return with the instantiated fs
    return result;
  }

  /** buildFS() produces the typed feature structure encoded in the stream in
   * jxchg format
   *
   * The string format that is recognized here is as follows:
   * <FS> := [ # <coref-no> ] '[' <type-no> (<feature-no> <FS>)* ']'
   *
   * @param gram a grammar that knows the valid types and features.
   * @return a TFS object
   * @throws {@link IOException}, {@link InvalidSyntaxException}
   */
  public static DagNode buildFS(JxchgTokenizer in, TFS contain)
    throws IOException, InvalidSyntaxException {
    ArrayList<DagNode> coref2Node = new ArrayList<DagNode>();
    // Java sux
    DagNode result = buildFS1(in, DagNode.getGrammar(), coref2Node, contain);
    return result;
  }

  public boolean sanityCheck() {
    final boolean result[] = { true };
    walkDag(new DagVisitorAdapter() {
      @Override
      public void startDag(DagNode here, DagNode deref, int corefNo) {
        result[0] = result[0]
            && here.getType() < fsgrammar.getNoOfGrammarTypes();
      }
    });
    return result[0];
  }
}
