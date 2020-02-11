package de.dfki.lt.loot.tfs;

public interface FSMassager {
  /** Apply destructive modifications to the fs, such as deletion of edges or
   *  type generalization under specific paths.
   *
   *  The method is supposed to handle intermediate dags correctly and do a
   *  proper (result) copy, which includes invalidation for the Tobabechi
   *  unifier.
   */
  TFS copyRestrict(TFS fs);

  TFS destructiveRestrict(TFS fs);

  TFS unifyRestrict(TFS fs, TFS arg, int argno);
}
