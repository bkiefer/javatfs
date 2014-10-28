package de.dfki.lt.loot.tfs.io;

import java.io.Writer;
import java.util.IdentityHashMap;

import de.dfki.lt.loot.tfs.DagNode;

public interface DagPrinter {
  
  public void toStringRec(DagNode dag, boolean readable, Writer sb,
      IdentityHashMap<DagNode, Integer> corefMap) ;
  
}
