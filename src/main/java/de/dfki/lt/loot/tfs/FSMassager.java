package de.dfki.lt.loot.tfs;

public interface FSMassager {
  // apply destructive modifications to the fs, such as restriction or
  // type generalization under specific paths
  TFS massage(TFS fs);
}
