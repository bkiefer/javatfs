package de.dfki.lt.loot.tfs;


import gnu.trove.procedure.TShortProcedure;
import gnu.trove.set.hash.TShortHashSet;

/** A very simple massager, that deletes all occurences of features in
 *  a deletion list.
 */
public class DelDtrsMassager implements FSMassager, DagRestrictor {

  public FSGrammar _grammar;

  // if feature is one of these, always delete
  public TShortHashSet _toDelete; // TODO: check if a simple array is faster

  @Override
  public int massageType(int fsType) {
    return fsType;
  }

  @Override
  public boolean keep(short feature, DagRestrictor child) {
    return (_toDelete == null) || !_toDelete.contains(feature);
  }

  public DagRestrictor.Iterator iterator() {
    return new DagRestrictor.Iterator() {

      @Override
      public DagRestrictor next(short feature) {
        // TODO Auto-generated method stub
        return DelDtrsMassager.this;
      }
    };
  }

  /** A private constructor. Use the factory method newMassager to obtain a
   *  MassageProvider
   */
  private DelDtrsMassager(FSGrammar grammar, TShortHashSet toDelete) {
    _grammar = grammar;
    _toDelete = toDelete;
  }

  public DagRestrictor dagRestrictor() { return this; }

  public TFS massage(TFS in) { return in.copyResult(this); }

  /** A factory method to obtain a new MassageProvider. The constructor is
   *  private, so this is the only way to get one.
   */
  public static DelDtrsMassager newMassager(FSGrammar grammar,
    String[] featuresToDelete) {
    TShortHashSet toDelete = null;
    if (featuresToDelete != null) {
      toDelete = new TShortHashSet();
      for (String feature : featuresToDelete)
        toDelete.add(grammar.getFeatureId(feature));
    }
    return new DelDtrsMassager(grammar, toDelete);
  }

  @Override
  public String toString() {
    final StringBuilder sb = new StringBuilder();
    if (_toDelete != null && ! _toDelete.isEmpty()) {
      sb.append("Del. features: ");
      _toDelete.forEach(new TShortProcedure() {

        @Override
        public boolean execute(short value) {
          sb.append(" ").append(_grammar.getFeatureName(value));
          return true;
        }
      });
      sb.append("\n");
    }
    return sb.toString();
  }

  @Override
  public TFS copyRestrict(TFS fs) {
    return fs.copyResult(this);
  }

  @Override
  public TFS destructiveRestrict(TFS fs) {
    // TODO not very efficient
    return fs.copyResult(this);
  }

  @Override
  public TFS unifyRestrict(TFS in, TFS arg, int argno) {
    TFS newTFS = null;
    if (in.unifyOnly(arg, argno)) {
      // this also has to do result copying, which includes invalidation
      newTFS = in.copyResult(this);
    } else {
      // requires invalidation in case of failure
      in.invalidate();
    }
    return newTFS;
  }

}
