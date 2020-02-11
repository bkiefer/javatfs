package de.dfki.lt.loot.tfs;

import gnu.trove.procedure.TShortProcedure;
import gnu.trove.set.hash.TShortHashSet;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.IdentityHashMap;

import de.dfki.lt.loot.tfs.DagNode.RESTRICT;


public class FullMassager implements FSMassager {

  public FSGrammar _grammar;

  // if feature is one of these, always delete
  public TShortHashSet _toDelete; // TODO: check if a simple array is faster

  // The root of the massage dag
  public FullRestrictor _root;

  /** This is a "null" massager that keeps everything beyond some point */
  public FullRestrictor noMassager;

  private class FullRestrictor implements DagRestrictor {

    // the feature that lead to this massager, -1 if the first massager for a
    // node (after descend)
    private short _feature;

    // The list of types to generalize for this node
    private int[] _toGeneralize;

    // type of restriction to apply at this node, if any
    private DagNode.RESTRICT _restr = DagNode.RESTRICT.RSTR_NO;

    // next massager in the preorder, one level down
    FullRestrictor _children[];

    private FullRestrictor(short feature) { _feature = feature; }

    private FullRestrictor() { this((short)-1); }

    private void addRestrictorDag(DagNode restrictor,
      IdentityHashMap<DagNode, FullRestrictor> visited) {
      visited.put(restrictor, this);

      //java.util.Iterator<DagEdge> arcIt = restrictor.getEdgeIterator();
      int size = 0;
      for(java.util.Iterator<DagEdge> arcIt = restrictor.getEdgeIterator();
          arcIt.hasNext();
          ++size, arcIt.next()) {}
      if (size > 0) _children = new FullRestrictor[size];

      String valString = _grammar.getTypeName(restrictor.getType());
      // already done when reading structures
      //if (valString.startsWith("\""))
      //  valString = valString.substring(1, valString.length() - 1);
      String[] types = valString.split(",");
      int start = 0;
      // if a restrictor type is specified, it must be the first
      try {
        _restr = DagNode.RESTRICT.valueOf(types[0].toUpperCase());
        start = 1;
      } catch (IllegalArgumentException ex) {
        _restr = RESTRICT.values()[0];
      }
      if (start < types.length) {
        _toGeneralize = new int[types.length - start];
        for (int i = start; i < types.length; ++i) {
          _toGeneralize[i - start] = _grammar.getTypeId(types[i]);
        }
      }

      java.util.Iterator<DagEdge> arcIt = restrictor.getEdgeIterator();
      for (int i = 0; arcIt.hasNext(); ++i) {
        DagEdge e = arcIt.next();
        DagNode sub = e.getValue();
        FullRestrictor coref = visited.get(sub);
        FullRestrictor child = new FullRestrictor(e.getFeature());
        if (coref == null) {
          child.addRestrictorDag(sub, visited);
        } else {
          child._restr = coref._restr;
          child._toGeneralize = coref._toGeneralize;
          child._children = coref._children;
        }
        _children[i] = child;
      }
    }

    public FullRestrictor fromRestrictorDag(DagNode restrictor) {
      FullRestrictor result = new FullRestrictor((short)-1);
      result.addRestrictorDag(restrictor,
          new IdentityHashMap<DagNode, FullRestrictor>());
      return result;
    }

    @Override
    public int massageType(int fsType) {
      if (_toGeneralize == null)
        return fsType;
      for (int type : _toGeneralize)
        if (_grammar.subsumesType(type, fsType))
          return type;
      return fsType;
    }

    @Override
    public boolean keep(short feature, DagRestrictor child) {
      FullRestrictor sub = (FullRestrictor) child;
      boolean globalKeep = (_toDelete == null)
                           || !_toDelete.contains(feature);
      if (! globalKeep)
        return false;

      boolean keep =
      // NO: keep all except those that explicitely specify deletion
          ((_restr == DagNode.RESTRICT.RSTR_NO
            && (sub._feature != feature
                || sub._restr != DagNode.RESTRICT.RSTR_DEL))
           || (_restr == DagNode.RESTRICT.RSTR_KEEP
               && sub._feature == feature));
      return keep;
    }

    public DagRestrictor.Iterator iterator() {
      return new FullMassagerIterator(this);
    }


    private void toStringRec(StringBuilder sb, int indent,
      IdentityHashMap<FullRestrictor, String> visited,
      String path) {
      // for(int i = 0;i <indent; ++i) sb.append(' ');
      if (visited.containsKey(this)) {
        sb.append("%").append(visited.get(this)).append("%");
      } else {
        visited.put(this, path);

        sb.append("[\"").append(_restr.toString());
        if (_toGeneralize != null)
          for (int t : _toGeneralize)
            sb.append(',').append(_grammar.getTypeName(t));
        sb.append("\"");

        if (_children != null) {
          int i = 0;
          while (i < _children.length) {
            FullRestrictor next = _children[i++];
            String feat = _grammar.getFeatureName(next._feature);
            sb.append('\n');
            for(int in = 0; in <indent; ++in) sb.append(' ');
            sb.append(feat).append(" ");
            next.toStringRec(sb, indent + feat.length() + 2, visited,
                path + '.' + feat);
          }
        }
        // for(int i = 0;i <indent; ++i) sb.append(' ');
        sb.append("] ");
      }
    }

    @Override
    public String toString() {
      IdentityHashMap<FullRestrictor, String> visited =
          new IdentityHashMap<>();
      StringBuilder sb = new StringBuilder();
      toStringRec(sb, 1, visited, "");
      return sb.toString();
    }
  }


  private class FullMassagerIterator implements DagRestrictor.Iterator {
    private FullMassager.FullRestrictor[] _children;
    private int _current;

    public FullMassagerIterator(FullMassager.FullRestrictor parent) {
      _children = parent._children;
      _current = _children == null ? -1 : 0;
    }

    public DagRestrictor next(short feature) {
      while (_current >= 0 && _current < _children.length
          && _children[_current]._feature < feature) {
        ++_current;
      }
      if (_current >= 0 && _current == _children.length) _current = -1;
      if (_current < 0 || _children[_current]._feature != feature)
        return noMassager;
      return _children[_current];
    }
  }

  /** A private constructor. Use the factory method newMassager to obtain a
   *  MassageProvider
   */
  private FullMassager(FSGrammar grammar, TShortHashSet toDelete,
      DagNode restrictorDag) {
    _grammar = grammar;
    _toDelete = toDelete;

    _root = noMassager = new FullRestrictor() {
      @Override
      public int massageType(int type) { return type; }

      @Override
      public boolean keep(short feature, DagRestrictor sub) {
        return ((_toDelete == null) || !_toDelete.contains(feature));
      }

      @Override
      public DagRestrictor.Iterator iterator() {
        return new DagRestrictor.Iterator() {
          @Override
          public DagRestrictor next(short feature) { return noMassager; }
        };
      }
    };

    if (restrictorDag != null)
      _root = new FullRestrictor().fromRestrictorDag(restrictorDag);
  }

  public DagRestrictor dagRestrictor() {
    return _root;
  }

  public TFS copyRestrict(TFS in) {
    return in.copyResult(_root);
  }

  public TFS unifyRestrict(TFS in, TFS arg, int argno) {
    TFS newTFS = null;
    if (in.unifyOnly(arg, argno)) {
      // this also has to do result copying, which includes invalidation
      newTFS = in.copyResult(_root);
    } else {
      // requires invalidation in case of failure
      in.invalidate();
    }
    return newTFS;
  }

  public TFS destructiveRestrict(TFS in) {
    // TODO: not very efficient
    return copyRestrict(in);
  }

  /*
  private void addPathsToGeneralize(LinkedHashMap<String, String> configPaths) {
    HashMap<List<Short>, List<Integer>> paths =
        new HashMap<List<Short>, List<Integer>>();

    for(Map.Entry<String, String> pathValue : configPaths.entrySet()) {
      String[] path = pathValue.getKey().split("\\.");
      List<Short> current = new ArrayList<Short>(path.length);
      if (pathValue.getKey() != "" && pathValue.getKey() != "<>") {
        for (String feat : path) {
          current.add(_grammar.getFeatureId(feat.trim()));
        }
      }
      String[] typeStrings = pathValue.getValue().split("\\,");
      List<Integer> types = new ArrayList<Integer>(typeStrings.length);
      for (String type: typeStrings) {
        types.add(_grammar.getTypeId(type));
      }
      paths.put(current, types);
    }
  }
  */

  /** A factory method to obtain a new MassageProvider. The constructor is
   *  private, so this is the only way to get one.
   */
  public static FullMassager newMassager(FSGrammar grammar,
    String[] featuresToDelete, TFS restrictor) {
    TShortHashSet toDelete = null;
    if (featuresToDelete != null) {
      toDelete = new TShortHashSet();
      for (String feature : featuresToDelete)
        toDelete.add(grammar.getFeatureId(feature));
    }
    return new FullMassager(grammar, toDelete,
        restrictor == null ? null : restrictor.dag());
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
    if (_root != null) sb.append(_root.toString());
    return sb.toString();
  }

}
