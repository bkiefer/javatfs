package de.dfki.lt.loot.tfs.util;

import java.util.ArrayList;
import java.util.Collections;

public class IntTrie<T> implements Comparable<IntTrie<T>> {

  // The value stored in this trie node
  int _value;
  // if this node is a final node, this is the id of its Info node
  T _finalId;
  // the children of this trie node
  ArrayList<IntTrie<T>> _subs;

  private IntTrie(int val) {
    _value = val;
    _subs = null;
    _finalId = null;
  }

  /** the _value in the root node contains the new ID counter of the trie, and
   *  the _finalId potentially the Kleene star character
   */
  public IntTrie() { this(0); }

  /** Set the kleene star character */
  // public setStar(char c) { _finalId = c; }


  /** helper for private addSequence method, returns a given sibling Trie node,]
   *  if one exists, or creates a new one.
   *
   *  TODO: Seeking is linear, might need improvement
   */
  public IntTrie<T> findOrAdd(int id) {
    IntTrie<T> node = null;
    if (_subs == null) {
      node = new IntTrie<T>(id);
      _subs = new ArrayList<IntTrie<T>>(1);
      _subs.add(node);
    } else {
      for (IntTrie<T> sub : _subs) {
        if (sub._value == id) {
          node = sub;
          break;
        }
      }
      if (node == null) {
        node = new IntTrie<T>(id);
        _subs.add(node);
      }
    }
    return node;
  }

  /** returns a sibling Trie node that has id as _value, if one exists, null
   *  otherwise.
   *
   *  TODO: Seeking is linear, might need improvement
   */
  private IntTrie<T> find(int id) {
    if (_subs != null) {
      for (IntTrie<T> sub : _subs) if (sub._value == id) return sub;
    }
    return null;
  }

  /** Find the node for the sequence, or null if it is not in the trie */
  public IntTrie<T> findSequence(int[] ids) {
    IntTrie<T> node = this;
    for (int id : ids) {
      node = node.find(id);
      if (node == null) break;
    }
    return node;
  }

  public T getValue(int[] ids) {
    IntTrie<T> node = findSequence(ids);
    if (node == null) return null;
    return node._finalId;
  }

  public void remove(int[] ids) {
    IntTrie<T> node = findSequence(ids);
    if (node != null) node._finalId = null;
  }

  /** private helper for public addSequence methods *
  private T addSequenceRec(int[] ids, T newId, int pos) {
    if (pos == ids.length) {
      if (_finalId == null)
        _finalId = newId;
      return _finalId;
    }
    IntTrie<T> node = findOrAdd(ids[pos]);
    return node.addSequenceRec(ids, newId, ++pos);
  }
  */

  /** Add this int sequence to the trie */
  public T addSequence(int[] ids, T newVal) {
    IntTrie<T> curr = this;
    for (int id : ids) {
      IntTrie<T> node = curr.find(id);
      if (node == null) {
        node = new IntTrie<T>(id);
        if (curr._subs == null) {
          curr._subs = new ArrayList<IntTrie<T>>(1);
        }
        curr._subs.add(node);
      }
      curr = node;
    }
    if (curr._finalId == null)
      curr._finalId = newVal;
    return curr._finalId;
  }


  /** walk a given branch or create one. Uses binarySearch for finding the
   *  right branch, and inserts in the right position for fast access.
   */
  public IntTrie<T> add(int val) {
    if (_subs == null) {
      _subs = new ArrayList<IntTrie<T>>();
      _subs.add(new IntTrie<T>(val));
      return _subs.get(0);
    }
    IntTrie<T> toFind = new IntTrie<T>(val);
    int pos = Collections.binarySearch(_subs, toFind);
    if (pos < 0) {
      pos = - pos - 1;
      _subs.add(pos, new IntTrie<T>(val));
    }
    return _subs.get(pos);
  }

  /** Add this int sequence to the trie */
  public T getOrAdd(int[] seq, T newVal) {
    T newId = addSequence(seq, newVal);
    return newId;
  }

  /** Add the char sequence of string to this trie (interpreted as int[]) */
  public T getOrAdd(String string, T newVal) {
    string.toCharArray();
    int[] seq = new int[string.length()];
    for(int i = 0; i < seq.length; ++i) {
      seq[i] = string.charAt(i);
    }
    return getOrAdd(seq, newVal);
  }

  @Override
  public int compareTo(IntTrie<T> o2) { return this._value - o2._value; }

  /** Optimize trie for fast access */
  public void optimize() {
    if (_subs == null) return;
    Collections.sort(_subs);
    for (IntTrie<T> sub : _subs) sub.optimize();
  }

  public int size() {
    return _value;
  }

  @Override
  public String toString() {
    return "" + _value + ":" + _finalId;
  }

  public void walkTrie(IntTrieWalker<T> walker) {
    walker.startNode(this);
    if (_subs != null) {
      for (IntTrie<T> val : _subs) {
        walker.beforeEdge(val._value);
        val.walkTrie(walker);
        walker.afterEdge(val._value);
      }
    }
    walker.endNode(this);
  }


  /* ######################################################################
   * DictIterator methods
   * ###################################################################### */

  /** try to find a continuation of the current node */
  public IntTrie<T> extend(int val) {
    if (_subs == null)
      return null;
    IntTrie<T> toFind = new IntTrie<T>(val);
    int pos = Collections.binarySearch(_subs, toFind);
    return pos < 0 ? null : _subs.get(pos);
  }

  /** Return the id corresponding to this node */
  public T getValue() {
    return _finalId;
  }

  /** Set the value stored in this node to val */
  public void setValue(T val) {
    _finalId = val;
  }

  /** is this a final node? */
  public boolean isFinal() {
    return _finalId != null;
  }
}
