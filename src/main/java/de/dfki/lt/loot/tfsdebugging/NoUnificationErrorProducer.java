package de.dfki.lt.loot.tfsdebugging;

import de.dfki.lt.loot.tfs.TFS;

public class NoUnificationErrorProducer extends AbstractTFSErrorProducer {
  // two tfs that should have a unification result fail
  public NoUnificationErrorProducer(TFS[] infs) {
    super(infs, infs.length);
  }
  
  public boolean errorPersists() {
    TFS[] restr = getRestricted();
    
    TFS result = restr[0].unifyFS(restr[1], 0);

    //Map<? extends de.dfki.lt.loot.gui.TypedFS, DagNode.FailType> fwfails = 
    //  tfs1.dag().getForwardFails();
    return (result == null);
  }
}
