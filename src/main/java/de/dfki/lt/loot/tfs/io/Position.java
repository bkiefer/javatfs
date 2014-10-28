package de.dfki.lt.loot.tfs.io;

public class Position {

  public String loc;
  public int line;
  public int column;
  public String msg;

  public Position(int l, int c, String s, String m) {
    msg = m; line = l; column = c; loc = s;
  }

  public Position(int l, int c, String m) {
    this(l, c, m, null);
  }
  
  @Override
  public boolean equals(Object o) {
    if (! (o instanceof Position)) return false;
    Position p2 = (Position) o;
    if (msg != null) {
      if (! msg.equals(p2.msg)) return false;
    } else {
      if (p2.msg != null) return false;
    }
    if (loc != null) {
      if (! loc.equals(p2.loc)) return false;
    } else {
      if (p2.loc != null) return false;
    }
    return line == p2.line && column == p2.column;
  }

  @Override
  public int hashCode() {
    return line << 10 + column + (loc == null ? 0 : loc.hashCode())
        + (msg == null ? 0 : msg.hashCode());
  }

  public String toString() {
    return ((loc == null) ? "" : loc + ":") + line + ":" + column
        + ((msg == null) ? "" : ": " + msg);
  }
}
