package de.dfki.lt.loot.tfs.io;

import de.dfki.lt.loot.tfs.TFS;

public interface TfsConsumer extends Consumer {
  
  /** consume the next tfs from the reader */
  public abstract void consume(TFS fs);
  
  /** if there's an internal limit to my consummation, i can signal it here */
  public abstract boolean atEnd();
}
