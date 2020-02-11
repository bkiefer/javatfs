package de.dfki.lt.loot.tfs;

import gnu.trove.list.TIntList;

/** A class for thread-safe dags, in a single int array,
 *  the representation is as follows:
 *
 *  _nodes:
 *  0: type of node 0
 *  1: offset to edge list of node 0: i , or -1, if no edges
 *  ...
 *
 *  0: no edges of node 0
 *  1: feature id of edge 0 of node 0
 *  2: id of target node of edge 0
 *  ...
 * @author kiefer
 *
 */
public class Dag {
  int[] _nodes;
  int[] _edges;

  /** For thread safety, these will later be thread local */
  static TIntList _tempNodes;
  static TIntList _tempEdges;

  public static Dag DagnodeToDag(DagNode input) {
    int currNode = 0, currEdge = 0;
    return null;
  }

}
