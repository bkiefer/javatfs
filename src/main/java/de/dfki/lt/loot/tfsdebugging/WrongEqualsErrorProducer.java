package de.dfki.lt.loot.tfsdebugging;

import de.dfki.lt.loot.tfs.DagNode;
import de.dfki.lt.loot.tfs.TFS;

public class WrongEqualsErrorProducer extends AbstractTFSErrorProducer {

  // two tfs differ in what equals says in contrast to subsumesBi
  public WrongEqualsErrorProducer(TFS[] infs) {
    super(infs, 1);
  }

  @Override
  public boolean errorPersists() {
    TFS[] currtfs = getRestricted();
    boolean subsresult = (currtfs[0].subsumesBi(currtfs[1])
        == (DagNode.THIS_MORE_GENERAL | DagNode.ARG_MORE_GENERAL));
    boolean eqresult = currtfs[0].equals(currtfs[1]);
    return (subsresult != eqresult);
  }

}
