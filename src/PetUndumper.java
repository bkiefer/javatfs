package de.dfki.lt.loot.tfs.io;

import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.Charset;

import org.apache.log4j.Logger;

import de.dfki.lt.loot.tfs.FSGrammar;

/**
 * ShUG (for Shallow Unification Grammars) is a collection of objects and
 * methods that allows to read in the binary output of the flop preprocessor of
 * the PET system; since the constraints for the types as well as the type
 * hierarchy for a given UBG are explicitly represented in Java, there is no
 * longer a need to have native methods that call (some of) the basic
 * functionality of PET, such as type unification; note that this new version of
 * ShUG supports different character encodings (thanks Witold!)
 *
 * version 2 of ShUG replaces the static class fields BOTTOM_CODE and
 * STRING_TYPE by instance fields bottomCode and stringType
 *
 * @see FSGrammar
 *
 * @author (C) Hans-Ulrich Krieger
 * @since JDK 1.5
 * @version 5.0.0, Tue Jul 26 14:50:21 CEST 2005
 */
public class PetUndumper {

  private static final Logger LOGGER = Logger.getLogger(PetUndumper.class);

  /**
   * this protected field allows to set the character encoding; its default
   * value is "ISO-8859-1"; other useful values might be "UTF-8" or "EUC-JP"
   */
  protected String charsetName;

  /**
   * given the instance field this.charsetName, this.charset holds the
   * corresponding java.nio.charset.Charset object
   */
  protected Charset charset;

  /**
   * for easy and fast access of the binary output of the flop preprocessor of
   * PET, we map the binary file onto an internalized byte array that is cleared
   * after the objects have been established in memory
   */
  private byte[] randomAccessFile;

  /**
   * this instance field represents the length of the binary file in bytes
   */
  private int maxLength;

  /**
   * this instance field represents the file pointer to the internal byte array
   * randomAccessFile
   */
  private int filePointer;

  /**
   * offset from position zero, saying where the symbol table starts in
   * randomAccessFile
   */
  protected int symtabOffset;

  /**
   * offset from position zero, saying where the print names start in
   * randomAccessFile
   */
  protected int printnamesOffset;

  /**
   * offset from position zero, saying where the type hierarchy starts in
   * randomAccessFile
   */
  protected int hierarchyOffset;

  /**
   * offset from position zero, saying where the feature tables start in
   * randomAccessFile (currently not used)
   */
  protected int feattabsOffset;

  /**
   * offset from position zero, saying where the full forms start in
   * randomAccessFile (currently not used)
   */
  protected int fullformsOffset;

  /**
   * offset from position zero, saying where the inflection rules start in
   * randomAccessFile (currently not used)
   */
  protected int inflrOffset;

  /**
   * offset from position zero, saying where the type constraints start in
   * randomAccessFile
   */
  protected int constraintsOffset;

  /**
   * offset from position zero, saying where the irregs start in
   * randomAccessFile (currently not used)
   */
  protected int irregsOffset;

  // BEGIN constructor

  public PetUndumper(String aCharsetName) {
    if (Charset.isSupported(aCharsetName)) {
      this.charsetName = aCharsetName;
      this.charset = Charset.forName(this.charsetName);
    }
  }

  /**
   * allows to directly further specify the character encoding
   */
  public PetUndumper() {
    // could not use the this() notation to call the above constructor,
    // since it has to be the first statement, hence setting the encoding
    // afterwards is too late ...
    // now construct the global tables, ...
    this("ISO-8859-1");
  }


  // BEGIN getter/setter

  /**
   * given a filename (which refers to the binary output of the flop
   * preprocessor of PET), ShUG() reads in (1) header (2) table of content (3)
   * symbol tables (4) type hierarchy (5) type constraints there exists a short
   * and partly outdated description of this binary representation in Uli
   * Callmeier's masters thesis
   *
   * @see "U. Callmeier: Efficient Parsing with Large-Scale Unification, Masters
   *      Thesis, Universitaet des Saarlandes, 2001"
   * @param   filename
   *          the file name of a binary grm file that is produced by the PET
   *          preprocessor flop
   */
  public void open(String filename) throws IOException {
    File file = new File(filename);
    this.maxLength = (int) file.length();
    LOGGER.info("grammar file size: " + this.maxLength + " bytes");
    // create byte array of appropriate size
    this.randomAccessFile = new byte[this.maxLength];
    BufferedInputStream stream =
      new BufferedInputStream(new FileInputStream(file));
    // fully read in byte stream
    stream.read(this.randomAccessFile, 0, this.maxLength);
    stream.close();
  }

  public void close() {
    this.randomAccessFile = null;
  }

  /**
   * returns the character encoding (e.g., "UTF-8") set by setCharEncoding();
   * default value is "UTF-8"
   */
  public String getCharEncoding() {
    return this.charsetName;
  }

  /**
   * explicitly sets the character encoding (e.g., "UTF-8") of the ShUG grammar
   * object; setting the encoding must be achieved before loading the grm binary
   * file; you can achieve this in your program as follows: ShUG grammar = new
   * ShUG(); grammar.setCharEncoding(charsetName);
   * grammar.loadGrammar(fileName);
   */
  public void setCharEncoding(String aCharsetName) {
    this.charsetName = aCharsetName;
    if (Charset.isSupported(charsetName))
      this.charset = Charset.forName(charsetName);
  }

  // END getter/setter

  // BEGIN undump/offset

  /**
   * since Java does not support unsigned bytes and since shorts and ints come
   * in as a sequence of bytes, we need a method that returns an int
   * representing the unsigned byte
   */
  protected int makeUnsigned(byte b) {
    if (b < 0)
      return 127 + (b & 127) + 1;

    return b;
  }

  /** a short is encoded as a sequence of two bytes */
  @SuppressWarnings("cast")
  public short undumpShort() {
    byte[] ba = new byte[2];
    ba[0] = this.randomAccessFile[this.filePointer++];
    ba[1] = this.randomAccessFile[this.filePointer++];
    return (short) (((short) ba[1] << 8) + makeUnsigned(ba[0]));
  }

  /** an int is encoded as a sequence of four bytes */
  public int undumpInt() {
    byte[] ba = new byte[4];
    ba[0] = this.randomAccessFile[this.filePointer++];
    ba[1] = this.randomAccessFile[this.filePointer++];
    ba[2] = this.randomAccessFile[this.filePointer++];
    ba[3] = this.randomAccessFile[this.filePointer++];
    return (((((ba[3] << 8) + makeUnsigned(ba[2])) << 8)
             + makeUnsigned(ba[1])) << 8)
           + makeUnsigned(ba[0]);
  }

  /**
   * undumpString() dispatches between character sets known by java.nio.charset
   * and java.io
   */
  public String undumpString() {
    if (Charset.isSupported(this.charsetName))
      return undumpStringFast();

    return undumpStringSlow();
  }

  /**
   * a string is preceded by a short, telling us how many characters must be
   * read in order to reconstruct the string
   */
  public String undumpStringFast() {
    // strings in the binary representation of PET are terminated by the NULL
    // character;
    // hence undump the last character, but do NOT store it
    int length = undumpShort() - 1;
    // allocate a byte buffer of 'length' bytes
    ByteBuffer bb = ByteBuffer.allocate(length);
    for (int s = 0; s < length; s++)
      bb.put(this.randomAccessFile[this.filePointer++]);
    this.filePointer++; // read off null character
    bb.rewind();
    CharBuffer cb = this.charset.decode(bb);
    return cb.toString();
  }

  /**
   * thanks to Witold, this string undumper even works for "EUC-JP" due to the
   * fact that it uses java.io (instead of java.nio and java.nio.charset), but
   * is unfortunately very slooooooooow
   */
  public String undumpStringSlow() {
    int length = undumpShort() - 1;
    int realLength = 0;
    char[] ca = new char[length];
    int i;
    ByteArrayInputStream pBAIS = new ByteArrayInputStream(
        this.randomAccessFile, filePointer, length);
    filePointer += length;
    try {
      InputStreamReader pISR = new InputStreamReader(pBAIS, getCharEncoding());
      BufferedReader in = new BufferedReader(pISR);
      for (int s = 0; s < length; s++) {
        i = in.read();
        if (i == -1) {
          break;
        }
        ca[s] = (char) i;
        realLength++;
      }
      this.filePointer++;
      char ca2[] = new char[realLength];
      System.arraycopy(ca, 0, ca2, 0, realLength);
      return new String(ca2);
    } catch (Exception err) {
      PetUndumper.LOGGER.error("error while undumping string: " + err);
    }
    return "error reading string";
  }

  /**
   * the instance field codesize tells us how long the int array for the code
   * will be; it further tells us how many ints must be read before the end
   * markers (int zero plus short zero) show up (which must also be read); a
   * bitcode comes in as a sequence of integers, whereas succeeding zeros are
   * represented as an int zero, followed by a short, telling us how many int
   * zeros must be entered into the int array
   *
   * @see #readHierarchy
   */
  public int[] undumpBitcode(int codesize) {
    int[] code = new int[codesize];
    int pos = 0;
    int length;
    while (pos < codesize) {
      code[pos] = undumpInt();
      // run-length encoding for zeros
      if (code[pos] == 0) {
        length = undumpShort();
        while (--length > 0) {
          pos++;
          if (pos >= codesize) {
            PetUndumper.LOGGER.error("invalid compressed bitcode (too long)");
            System.exit(1);
          }
          code[pos] = 0;
        }
      }
      pos++;
    }
    // end marker test
    if ((undumpInt() != 0) || (undumpShort() != (short) 0)) {
      PetUndumper.LOGGER.error("invalid compressed bitcode (no end marker)");
      System.exit(1);
    }
    return code;
  }

  /**
   * parameter j refers to the jth position in the global node array
   * this.featureStructures; when we undump a node for position j, it is
   * guaranteed that an initial feature structure for this position has already
   * been created
   *
  protected void undumpNode(int j) {
    TFS fs = this.featureStructures[j];
    // set the type
    fs.setType(undumpInt());
    // now read out the top-level arcs (feature-value pairs), i.e., pairs of
    // feature name
    // identifiers and node ids which refer to a position in the node array and
    // add them
    // top-level to FS fs
    short noArcs = undumpShort();
    for (short i = (short) 0; i < noArcs; i++) {
      // TODO creation of ITFS's might be optimized here using the
      // difference of j and the result of undumpShort() as numbering
      fs.addEdge(undumpShort(), this.featureStructures[undumpShort()]);
    }
  }
   */

  /**
   * make absolute offset for global byte array this.randomAccessFile;
   *
   * @return the value of parameter offset iff offset <= length of
   *         this.randomAccessFile; -1 otherwise
   */
  public int makeAbsoluteOffset(int offset) {
    return (offset > this.maxLength) ? -1 : (this.filePointer = offset);
  }

  /**
   * make relative offset for global byte array this.randomAccessFile;
   *
   * @return offset + this.filePointer iff offset + this.filePointer <= length
   *         of this.randomAccessFile; -1 otherwise
   */
  protected int makeRelativeOffset(int offset) {
    int newFilePointer = this.filePointer + offset;
    return (newFilePointer > this.maxLength ? -1
        : (this.filePointer = newFilePointer));
  }

  // END undump/offset

}
