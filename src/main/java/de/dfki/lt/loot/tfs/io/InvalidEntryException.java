package de.dfki.lt.loot.tfs.io;

public class InvalidEntryException extends Exception {
  private static final long serialVersionUID = 7733507456235991472L;

  public InvalidEntryException() {
    super();
  }

  public InvalidEntryException(String msg) {
    super(msg);
  }

}
