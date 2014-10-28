package de.dfki.lt.loot.tfsdebugging;

import de.dfki.lt.loot.tfs.TFS;

public class SubsumptionErrorProducer extends AbstractTFSErrorProducer {
  private int correct;
    
  public SubsumptionErrorProducer(TFS[] infs, int correctAnswer) {
    super(infs, 1); // only one restrictor for all fs's
    correct = correctAnswer;
  }
  
  public boolean errorPersists() {
    TFS[] restr = getRestricted();
    
    int result = restr[0].subsumesBi(restr[1]);
    //Map<? extends de.dfki.lt.loot.gui.TypedFS, DagNode.FailType> fwfails = 
    //  tfs1.dag().getForwardFails();
    return (result == correct);
  }
}
