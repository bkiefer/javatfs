package de.dfki.lt.loot.tfs.io;

import java.util.List;

import de.dfki.lt.loot.tfs.TFS;

/** A consumer for reading the full JXCHG format containing a whole parse chart
 *  or an equivalent of it
 */
public interface EdgeConsumer extends Consumer {
  void setChartSize(int size);
  void addEdge(int id, int start, int end, String ruleName,
      List<?> subEdges, TFS fs) throws InvalidEntryException ;
}
