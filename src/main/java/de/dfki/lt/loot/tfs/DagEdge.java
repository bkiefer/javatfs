package de.dfki.lt.loot.tfs;

public class DagEdge implements Comparable<DagEdge> {
  /** a <b>feature</b> (sometimes called attribute or a label) is internally
   * represented as a short, usually starting with 0 */
  short feature;

  /** a <b>value</b> is an instance of class DagNode */
  DagNode value;

  // BEGIN constructor

  /**
   * the binary creator
   * @param feature the feature of a FVPair object, represented as a short
   * @param value the value of a FVPair object, a DagNode object
   */
  public DagEdge(short feat, DagNode val) {
    this.feature = feat;
    this.value = val;
  }

  // END constructor

  /** the public getter for the private member field feature; */
  public short getFeature() { return this.feature; }

  /** the public getter for the private member field feature; */
  public String getName() {
    return de.dfki.lt.loot.tfs.DagNode
    .getGrammar().getFeatureName(this.feature);
  }

  /** the public getter for private member field value */
  public DagNode getValue() { return this.value; }

  /** the public setter for private member field value */
  public DagNode setValue(DagNode val) {
    this.value = val;
    return val;
  }

  public int compareTo(DagEdge o) {
    return (this.feature - o.feature);
  }

  public boolean isFirst() {
    return getFeature() == DagNode.fsgrammar.firstFeatureId;
  }
  public boolean isRest() {
    return getFeature() == DagNode.fsgrammar.restFeatureId;
  }

  @Override
  public String toString() {
    return getName() + ": " + getValue();
  }

}

