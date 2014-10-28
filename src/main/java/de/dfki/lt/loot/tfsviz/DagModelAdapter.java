package de.dfki.lt.loot.tfsviz;

import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.dfki.lt.loot.Pair;
import de.dfki.lt.loot.gui.adapters.MapAdapterIterator;
import de.dfki.lt.loot.gui.adapters.ModelAdapter;
import de.dfki.lt.loot.gui.adapters.ModelAdapterFactory;
import de.dfki.lt.loot.tfs.DagEdge;
import de.dfki.lt.loot.tfs.DagNode;
import de.dfki.lt.loot.tfs.DagNode.FailType;

public class DagModelAdapter extends ModelAdapter {

  public static void init() {
    ModelAdapterFactory.registerAdapter(DagNode.class, DagModelAdapter.class);
  }

  private class EdgeAdapterIterator implements MapAdapterIterator {
    short[] _excludedFeatures;
    Pair<Object, Object> _current;
    private Iterator<? extends DagEdge> _iterator;

    /** precondition: _iterator != null */
    private void advance() {
      _current = null;
      while (_current == null && _iterator.hasNext()) {
        DagEdge edge = _iterator.next();
        if (_excludedFeatures == null ||
            Arrays.binarySearch(_excludedFeatures, edge.getFeature()) == -1)
          _current = new Pair<Object, Object>(edge, edge.getValue());
      }
    }

    public EdgeAdapterIterator(DagNode node) { this(node, null); }

    public EdgeAdapterIterator(DagNode node, String[] excludedFeatures) {
      _current = null;
      _iterator = node.getEdgeIterator();
      if (_iterator != null) {
        if (excludedFeatures != null) {
          _excludedFeatures = new short[excludedFeatures.length];
          int i = 0;
          for (String feat : excludedFeatures) {
            _excludedFeatures[i] = DagNode.getGrammar().getFeatureId(feat);
          }
          Arrays.sort(_excludedFeatures);
        }
        advance();
      }
    }

    public boolean hasNext() { return _current != null; }

    public Pair<Object, Object> next() {
      Pair<Object, Object> result = _current;
      advance();
      return result;
    }
  }

  private class MapMarker {
    DagNode _root;
    MapMarker(DagNode root) { _root = root; }
  }

  @Override
  public int facets(Object model) {
    if (model instanceof MapMarker) {
      return ModelAdapter.MAP;
    }
    if (model instanceof DagNode) {
      DagNode node = (DagNode) model;
      if (node.getNewType() == DagNode.getGrammar().getConsType())
        return ModelAdapter.MAP | ModelAdapter.CONS;
      if (node.getNewType() == DagNode.getGrammar().getNullType())
        return ModelAdapter.MAP | ModelAdapter.NULL;
      if (node.getNthArg(0) != null)
        return ModelAdapter.MAP | ModelAdapter.TREE;
      return ModelAdapter.MAP;
    }
    if (model instanceof DagEdge) {
      return ModelAdapter.SYMBOL;
    }
    return ModelAdapter.NONE;
  }

  public String getString(Object model) {
    assert(model instanceof DagEdge);
    return ((DagEdge)model).getName();
  }
  
  @Override
  public String getAttribute(Object model, String name) {
    DagNode node;
    if (model instanceof MapMarker) {
      node = ((MapMarker) model)._root;
    } else if (model instanceof DagNode) {
      node = (DagNode) model;
    } else if (model instanceof DagEdge) {
      // for future extensions
      return null;
    } else {
      return null;
    }

    switch (name.charAt(0)) {
    case 't' : return node.getTypeName();
    case 'f' : {
      FailType ft = DagNode.forwardFailures.get(node);
      return (ft == null ? null : ft.toString());
    }
    case 'b' : {
      FailType bt = DagNode.backwardFailures.get(node);
      return (bt == null ? null : bt.toString());
    }
    }
    return null;
  }

  @Override
  public Object getFirst(Object model) {
    DagNode node = (DagNode) model;
    Iterator<? extends DagEdge> it = node.getEdgeIterator();
    if (it == null) return null;
    while (it.hasNext()) {
      DagEdge edge = it.next();
      if (edge.isFirst()) return edge.getValue();
    }
    return null;
  }

  @Override
  public Object getRest(Object model) {
    DagNode node = (DagNode) model;
    Iterator<? extends DagEdge> it = node.getEdgeIterator();
    if (it == null) return null;
    while (it.hasNext()) {
      DagEdge edge = it.next();
      if (edge.isRest()) return edge.getValue();
    }
    return null;
  }

  @Override
  public Object getNodeContent(Object model) {
    return new MapMarker((DagNode) model);
  }

  @SuppressWarnings("rawtypes")
  @Override
  public Iterable getTreeDaughters(Object model) {
    // if (!(model instanceof TreeMarker)) return null;
    DagNode tree = (DagNode) model;
    List<DagNode> dtrs = new LinkedList<DagNode>();
    DagNode subnode = tree.getValue(DagNode.getGrammar().getArgsFeature());
    if (subnode == null) return null;
    while (subnode != null) {
      Iterator<? extends DagEdge> it = subnode.getEdgeIterator();
      if (it == null) break;
      subnode = null;
      while (it.hasNext()) {
        DagEdge edge = it.next();
        if (edge.isRest()) { subnode = edge.getValue(); }
        if (edge.isFirst()) { dtrs.add(edge.getValue()); }
      }
    }
    return dtrs;
  }


  //@Override
  //public boolean isNull(Object model) { return false; }

  @Override
  public MapAdapterIterator mapIterator(Object model) {
    if (model instanceof MapMarker) {
      final String[] exclude = { "ARGS" };
      return new EdgeAdapterIterator(((MapMarker) model)._root, exclude);
    }
    return new EdgeAdapterIterator((DagNode) model);
  }
}
