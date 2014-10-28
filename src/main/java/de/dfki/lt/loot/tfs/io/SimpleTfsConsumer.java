package de.dfki.lt.loot.tfs.io;

import java.util.ArrayList;
import java.util.List;

import de.dfki.lt.loot.tfs.TFS;

public class SimpleTfsConsumer implements TfsConsumer {

  private int _maxFS;
  
  private List<TFS> _result; 
  
  public SimpleTfsConsumer() {
    this(0);
  }
  
  public SimpleTfsConsumer(int maxFS) {
    _maxFS = maxFS;
    _result = new ArrayList<TFS>(); 
  }
    
  @Override
  public int added() {
    return _result.size();
  }

  @Override
  public void consume(TFS fs) {
    _result.add(fs);
  }

  @Override
  public boolean atEnd() {
    return (_maxFS > 0 &&  _maxFS >= _result.size());
  }
  
  public List<TFS> getTfsList() { return _result; } 

}
