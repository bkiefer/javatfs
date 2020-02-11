package de.dfki.lt.loot.tfs.io;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.StreamTokenizer;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.zip.GZIPInputStream;

import org.slf4j.Logger;

import de.dfki.lt.loot.tfs.TFS;

public class JxchgTokenizer {
  private int offset;

  private Reader _in;
  /** current stream position */
  private int _line;
  private int _column;

  /** Start position of the last token */
  private Position _startPos;

  /** print errors or only collect them */
  private boolean _quiet = false;

  /** log parsing errors to this logger, if not null */
  private Logger _logger = null;

  /** Information to generate useful error messages: input location */
  private String _inputDescription;

  /** All errors since the last reset */
  private List<Position> _lastErrors = new LinkedList<Position>();

  private int _nextChar;

  public String sval;

  public int nval;

  public int ttype;

  private int _saved = -1;

  private static class Location {
    @SuppressWarnings("unused")
    public Position begin, end;
  }

  public void yyerror (String msg) {
    _lastErrors.add(new Position(_line, _column, _inputDescription , msg));
    if (! _quiet && _logger == null) {
      System.out.println(getLastErrorPosition().msg);
    }
    else if (_logger != null) {
      _logger.error(getLastErrorPosition().msg);
    }
  }

  public void yyerror(Location loc, String msg) {
    Position beg = loc.begin;
    _lastErrors.add(new Position(beg.line, beg.column, beg.msg, msg));
    if (! _quiet && _logger == null) {
      System.out.println(getLastErrorPosition().msg);
    }
    else if (_logger != null) {
      _logger.error(getLastErrorPosition().msg);
    }
  }

  public void setInputReader(String inputDescription, Reader in) {
    _in = in;
    _inputDescription = inputDescription;
    _line = 1;
    _column = 0;
    _nextChar = ' ';
    _lastErrors.clear();
  }

  public JxchgTokenizer(Reader r) {
    setInputReader("None", r);
    /*
    super(r);
    parseNumbers();
    eolIsSignificant(false);
    wordChars(0x21,0x7f); //wordChars(0x21, 0x2f);
    this.ordinaryChar('#');
    this.ordinaryChar('[');
    this.ordinaryChar(']');
    this.ordinaryChar('(');
    this.ordinaryChar(')');

    offset = -1;
    /*
    _r = r;
    _buffer = new char[1024];
    _current = _lastread = 0;
    */
  }

  public static Reader getReader(File file)
      throws FileNotFoundException, IOException {
    return new InputStreamReader(
        file.getName().endsWith(".gz")
        ? new GZIPInputStream(new FileInputStream(file))
        : new FileInputStream(file));
  }


  /** Return a new tokenizer that is fed from a (probably gzip compressed)
   *  file. The method automatically selects the correct input stream.
   * @throws IOException
   * @throws FileNotFoundException
   */
  public static JxchgTokenizer getFSReader(File file)
      throws FileNotFoundException, IOException {
    return new JxchgTokenizer(getReader(file));
  }

  @SuppressWarnings("fallthrough")
  void readNext() throws IOException {
    _nextChar = _in.read(); ++_column;
    switch (_nextChar) {
    case -1: _nextChar = StreamTokenizer.TT_EOF; break;
    case '\n': _column = 0; ++_line; // fall through is intended
    case ' ':
    case '\t':
    case '\u000C':
    case '\r': _nextChar = ' ' ; break;
    }
  }

  void skipws() throws IOException {
    do {
      while (_nextChar == ' ') {
        readNext();
      }
    } while (_nextChar == ' ');
  }

  private void pushBack() {
    if (_saved != -1) {
      yyerror("Can not push back more than one token!");
    }
    _saved = ttype;
  }

  public int nextToken1() throws IOException {
    int res = nextToken();
    String tok = null;
    switch (res) {
    case StreamTokenizer.TT_EOF: tok="EOF"; break;
    case StreamTokenizer.TT_NUMBER: tok="NUM:"+nval; break;
    case StreamTokenizer.TT_WORD: tok="WORD:"+sval; break;
    default: tok=Character.toString((char) ttype);
    }
    System.out.println(tok);
    return res;
  }

  /** This tokenizer should recognize the following tokens:
   *  [0-9]+ : number
   *  "([^\\"]+|\\.)*" : string
   *  [a-zA-Z_]\\w* : symbol
   *  '[' ']' '(' ')' '#'
   *  all whitespace characters are skipped
   * @throws IOException
   */
  public int nextToken() throws IOException {
    if (_saved != -1) {
      int tmp = _saved;
      _saved = -1;
      return tmp;
    }

    sval = null; nval=0;
    skipws();
    _startPos = getCurrentPosition();
    switch (_nextChar) {
    case StreamTokenizer.TT_EOF:
    case '(':
    case ')':
    case '[':
    case ']':
    case '#': {
      int result = _nextChar;
      readNext();
      return (ttype = result);
    }
    case '"': {
      StringBuffer sb = new StringBuffer();
      readNext();
      while (_nextChar != '"') {
        if (_nextChar == '\\') {
          readNext();
        }
        if (_nextChar == StreamTokenizer.TT_EOF) {
          yyerror("unexpected end of input in string");
          return StreamTokenizer.TT_EOF;
        }
        sb.append((char) _nextChar);
        readNext();
      }
      readNext();
      sval = sb.toString();
      return (ttype = StreamTokenizer.TT_WORD);
    }
    }
    /*
    if (Character.isDigit(_nextChar)) {
      nval = _nextChar - '0';
      readNext();
      while (Character.isDigit(_nextChar)) {
        nval *= 10;
        nval += ( _nextChar - '0');
        readNext();
      }
      return (ttype = StreamTokenizer.TT_NUMBER);
    }
    */

    StringBuffer sb = new StringBuffer();
    boolean onlyDigits = true;
    while (! Character.isWhitespace(_nextChar)
           && _nextChar != '(' && _nextChar != ')'
           && _nextChar != '[' && _nextChar != ']' &&_nextChar != '#') {
      onlyDigits = onlyDigits && Character.isDigit(_nextChar);
      sb.append((char) _nextChar);
      readNext();
    }
    if (onlyDigits) {
      nval = Integer.parseInt(sb.toString());
      sval = null;
      return (ttype = StreamTokenizer.TT_NUMBER);
    }
    sval = sb.toString();
    nval= 0;
    return (ttype = StreamTokenizer.TT_WORD);
  }

  // check that next token of this is a string equal to what
  public void checkString(String what) throws InvalidSyntaxException {
    if (ttype != StreamTokenizer.TT_WORD || ! sval.equals(what))
      throw new InvalidSyntaxException(what, this);
  }

  public void checkNextString(String what)
  throws IOException, InvalidSyntaxException {
    nextToken(); checkString(what);
  }

  // check that next token of st is a string equal to what
  public int getInt() throws InvalidSyntaxException {
    if (ttype != StreamTokenizer.TT_NUMBER)
      throw new InvalidSyntaxException("number", this);
    return nval;
  }

  // check that next token of st is a string equal to what
  public int getNextInt()
  throws IOException, InvalidSyntaxException {
    nextToken(); return getInt();
  }

  // check that next token of st is a string equal to what
  public String getNextString()
  throws IOException, InvalidSyntaxException {
    nextToken();
    if (ttype != StreamTokenizer.TT_WORD)
      throw new InvalidSyntaxException("string", this);
    return sval;
  }

  public void checkToken(char token) throws InvalidSyntaxException {
    if (ttype != token)
      throw new InvalidSyntaxException(Character.toString(token), this);
  }

  public void checkNextToken(char token)
  throws IOException, InvalidSyntaxException {
    nextToken(); checkToken(token);
  }

  /** transforms a string representation of a parser chart (as
   * specified in the class header above) into an isomorphic Java chart;
   */
  public void readEdges(EdgeConsumer e)
  throws IOException, InvalidSyntaxException {
    // the first two tokens in the stream represent the number of start and
    // the end vertices of the chart, followed by a sequence of the chart edges
    offset = getNextInt();
    e.setChartSize(getNextInt() - offset);
    // now read the tokens from str, representing a sequence of edges of the
    // above form which exactly constitute the shortest path subgraph;
    // note that I ALWAYS assume that an edge comes exactly as <start> <end>
    // <weight> <tfs>, hence calling hasMoreTokens() again can be delayed
    // AFTER the construction of the TFS;
    nextToken();
    while (ttype != StreamTokenizer.TT_EOF) {
      // coref table needs to be cleared for every call to buildFS1()
      int id = getInt();
      int start = getNextInt();
      int end = getNextInt();
      StringWriter rulename = new StringWriter();
      rulename.append(getNextString());
      nextToken();
      if (ttype == '[') {
        rulename.append("[ ");
        nextToken();
        while (ttype == StreamTokenizer.TT_WORD) {
          rulename.append(sval);
          rulename.append(' ');
          nextToken();
        }
        checkToken(']'); rulename.append("]");
        nextToken();
      }
      checkToken('(');
      nextToken();
      List<Object> subEdges = new ArrayList<Object>(2);
      if (ttype == StreamTokenizer.TT_NUMBER) {
        // List of child edge IDs
        do {
          subEdges.add(Integer.valueOf(nval));
          nextToken();
        } while (ttype == StreamTokenizer.TT_NUMBER);
      } else {
        // List of terminal Names, terminated by ')'
        while (ttype == StreamTokenizer.TT_WORD) {
          subEdges.add(sval);
          nextToken();
        }
      }
      checkToken(')');
      TFS fs = TFS.buildFS(this);
      try {
        e.addEdge(id, start - offset, end - offset, rulename.toString(),
            subEdges, fs);
      }
      catch (InvalidEntryException ex) {
        Location loc = new Location();
        loc.begin = getStartPos();
        loc.end = getEndPos();
        yyerror(loc, ex.getMessage());
      }
      nextToken();
    }
    close();
  }

  public void readEdges(Consumer consumer)
      throws IOException, InvalidSyntaxException {
    if (consumer instanceof EdgeConsumer) {
      readEdges((EdgeConsumer) consumer);
    } else if (consumer instanceof TfsConsumer) {
      TfsConsumer tfsConsumer = (TfsConsumer)consumer;
      while (!atEOF() && !tfsConsumer.atEnd()) {
        tfsConsumer.consume(TFS.buildFS(this));
      }
    } else {
      // unknown consumer
      throw new NoSuchMethodError(
          "Unknown consumer for readEdges: " + consumer);
    }
  }

  public boolean atEOF() throws IOException {
    nextToken();
    if (ttype == StreamTokenizer.TT_EOF)
      return true;
    pushBack();
    return false;
  }

  private Position getCurrentPosition() {
    return new Position(_line, _column, _inputDescription);
  }

  public Position getLastErrorPosition() {
    if (_lastErrors.isEmpty()) {
      return null;
    }
    return _lastErrors.get(_lastErrors.size() - 1);
  }

  /** Return all errors since the last reset */
  public Collection<? extends Position> getAllErrorPositions() {
    return _lastErrors;
  }

  public Position getEndPos() {
    return getCurrentPosition();
  }

  public Position getStartPos() {
    return _startPos;
  }

  public int lineno() {
    return _startPos.line;
  }

  public int column() {
    return _startPos.column;
  }

  public void close() throws IOException {
    _in.close();
  }

}
