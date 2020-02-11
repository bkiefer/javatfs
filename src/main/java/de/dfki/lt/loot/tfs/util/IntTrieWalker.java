package de.dfki.lt.loot.tfs.util;

public interface IntTrieWalker<T> {

  /** Enter a node during a walk */
  public void startNode(IntTrie<T> node);

  /** Visit edge with value val before recursive descent */
  public void beforeEdge(int val);

  /** Visit edge with value val after recursive descent */
  public void afterEdge(int val);

  /** Visit the node after all its edges have been visited */
  public void endNode(IntTrie<T> node);
}
