package de.dfki.lt.loot.tfs.io;

import java.io.StreamTokenizer;

@SuppressWarnings("serial")
public class InvalidSyntaxException extends Exception {
  private static String ttypeToString(JxchgTokenizer jxchgTokenizer) {
    String what = "unknown thing";
    switch(jxchgTokenizer.ttype) {
    case StreamTokenizer.TT_WORD: what = jxchgTokenizer.sval; break ;
    case StreamTokenizer.TT_EOF: what = "end of file"; break ;
    case StreamTokenizer.TT_NUMBER: what = Double.toString(jxchgTokenizer.nval); break ;
    case StreamTokenizer.TT_EOL: what = "end of line"; break ;
    default: what = Character.toString((char)jxchgTokenizer.ttype); break ;
    }
    return what;
  }

  private InvalidSyntaxException(String expect, String what, int line, int column) {
    super("Expected `" + expect + "', got `" + what + "'"+ " at " + line
        + ":" + column);
  }

  public InvalidSyntaxException(String expect, JxchgTokenizer jxchgTokenizer) {
    this(expect, ttypeToString(jxchgTokenizer), jxchgTokenizer.lineno()
        ,jxchgTokenizer.column());
  }
}
