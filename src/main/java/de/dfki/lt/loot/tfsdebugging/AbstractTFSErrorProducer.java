package de.dfki.lt.loot.tfsdebugging;

import java.util.HashSet;

import de.dfki.lt.loot.tfs.DagNode;
import de.dfki.lt.loot.tfs.TFS;

public abstract class AbstractTFSErrorProducer implements ErrorProducer {

  protected TFS[] tfs;
  protected TFS[] restrictors;
    
  protected void initRestors(int restrictorNo) {
    restrictors = new TFS[restrictorNo];
    for (int i = 0 ; i < restrictors.length ; ++i) {
      restrictors[i] = new TFS(DagNode.RESTRICT.RSTR_NO.ordinal());
    }
  }
  
  protected void reduceAll() {
    if (! errorPersists()) {
      throw new IllegalStateException("reduce starts with error not present");
    }
    int resNo = 0;
    for (int i = 0 ; i < tfs.length ; ++i) {
      tfs[i].dag().reduceRec(this, restrictors[resNo].dag(),
          new HashSet<de.dfki.lt.loot.tfs.DagNode>());
      if (resNo + 1 < restrictors.length)
        ++resNo;
    }
  }
  
  protected void init(TFS[] inputFSs, int restrictorNo) {
    tfs = inputFSs;
    initRestors(restrictorNo);
  }
  
  protected AbstractTFSErrorProducer(TFS[] inputFSs, int restrictorNo) {
    init(inputFSs, restrictorNo);
  }
 
  /** when this constructor is used, don't forget to call init of this class */
  protected AbstractTFSErrorProducer() { }
  
  protected TFS[] getRestricted() {
    int tfsNo = 0, resNo = 0;
    TFS[] result = new TFS[tfs.length];
    while (tfsNo < tfs.length) {
      result[tfsNo] = tfs[tfsNo].cloneFS();
      result[tfsNo].restrict(restrictors[resNo]);
      ++tfsNo;
      if (resNo + 1 < restrictors.length)
        ++resNo;
    }
    return result;
  }
  
  /** A blueprint for the usage of errorPersists
  public abstract boolean errorPersists() {
    TFS[] restr = getRestricted();
    
    int result = restr[0].callTheBuggyFunctions(restr[1]);
    // check that result is still wrong
    return (result == correct);
  }
  */

  /** A blueprint for the usage of reduce, not sufficient for most applications
   */
  @Override
  public String reduce() {
    reduceAll();
    return reductionFinished();
  }
  
  protected String reductionFinished() {
    String nl = System.getProperty("line.separator");
    StringBuilder sb = new StringBuilder();
    TFS[] restr = getRestricted();
    for (TFS fs : restr) {
      sb.append(fs.toString());
      sb.append(nl);
    }
    sb.append(" --- Restrictors --- "); sb.append(nl);
    for (TFS fs : restrictors) {
      sb.append(fs.toString());
      sb.append(nl);
    }
    return sb.toString();
  }
}
