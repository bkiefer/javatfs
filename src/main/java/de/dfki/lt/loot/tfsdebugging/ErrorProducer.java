package de.dfki.lt.loot.tfsdebugging;

public interface ErrorProducer {
  public boolean errorPersists();
  public String reduce();
}
