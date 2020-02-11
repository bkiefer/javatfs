package de.dfki.lt.loot.tfs;

public interface DagRestrictor {

  /** possibly generalize the current type in the feature structure */
  public int massageType(int type);

  /** return true if the feature should be kept, false if it should be removed */
  boolean keep(short feature, DagRestrictor child);

  /** Iterate over the restrictors one level deeper */
  Iterator iterator();

  public interface Iterator {
    DagRestrictor next(short feature);
  }
}
