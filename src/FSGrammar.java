package de.dfki.lt.loot.tfs;

import gnu.trove.TIntArrayList;
import gnu.trove.TIntIntHashMap;
import gnu.trove.TLongIntHashMap;
import gnu.trove.TObjectHashingStrategy;
import gnu.trove.TObjectIntHashMap;
import gnu.trove.TShortHashSet;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.Reader;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.zip.GZIPInputStream;

import org.apache.log4j.Logger;

import de.dfki.lt.loot.tfs.io.EdgeConsumer;
import de.dfki.lt.loot.tfs.io.InvalidSyntaxException;
import de.dfki.lt.loot.tfs.io.JxchgTokenizer;
import de.dfki.lt.loot.tfs.io.PetUndumper;
import de.dfki.lt.loot.tfs.util.IntIDMap;
import de.dfki.lt.loot.tfs.util.ShortIDMap;

/** * ShUG (for Shallow Unification Grammars) is a collection of objects and
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
 * @author (C) Hans-Ulrich Krieger
 * @since JDK 1.5
 * @version 5.0.0, Tue Jul 26 14:50:21 CEST 2005
 */
public class FSGrammar {

  private static final Logger LOGGER = Logger.getLogger(FSGrammar.class);

  /** Sections in the binary dump files for different types of information:
   *  - symbol table
   *  - print names
   *  - type hierarchy
   *  - feature tables         (fixed arity encoding), not used at the moment
   *  - full forms             simple replacement for lexicon, not used
   *  - inflectional rules     not used
   *  - type constraints       the feature structures
   *  - irregular morphological entries
   *  - direct supertype table
   *  - chart dump section (chart edges with feature structures)
   */
  enum Section {
    NOSECTION, SYMTAB, PRINTNAMES, HIERARCHY,
    FEATTABS, FULLFORMS, INFLR, CONSTRAINTS,
    IRREGS, PROPERTIES, SUPERTYPES, CHART
  }

  /**
   * this protected field collects all information usually printed to system.out
   */
  protected final StringBuffer allMessages = new StringBuffer();

  /**
   * this protected field allows to set the character encoding; its default
   * value is "ISO-8859-1"; other useful values might be "UTF-8" or "EUC-JP"
   */
  protected static String defaultCharsetName = "ISO-8859-1";
  protected String charsetName;

  /**
   * given the instance field this.charsetName, this.charset holds the
   * corresponding java.nio.charset.Charset object
   */
  protected Charset charset;

  /**
   * this constant tells us how many bits are needed to represent an integer
   * number (is used to compute the value of the instance field codesize, see
   * below)
   */
  private static final int INT_SIZE = 32;

  /**
   * this class field represents the type code vector for the BOTTOM type
   * (usually an int vector of zeros of the proper size);
   *
   * @see #isBottomCode
   */
  protected int[] bottomCode;

  /**
   * since we cache the GLBs at run time, it is possible that for a given pair
   * of types (a pair of ints), the GLB (an int) has NOT already been computed;
   * in this case, the getter for the GLB table returns -2; note that the TOP
   * type code is usually 0 (see TOP_TYPE), whereas the BOTTOM
   * type code is -1 (see BOTTOM_TYPE)
   */
  protected static final int GLB_NOT_COMPUTED = -2;

  /**
   * typeIDMap establishes a one-to-one mapping from integers to type
   * names, i.e., to strings; these integers are internally used to represent
   * types in objects of class TFS; this member field is dynamically created
   * during the initialization phase and is needed when interfacing FSs to other
   * components of a system;
   *
   * @see DagNode
   */
  protected IntIDMap<String> typeIDMap;
  /**
   * featureIDMap establishes a mapping from shorts to feature
   * names, i.e., to strings; the shorts are internally used to represent
   * features in objects of class FeatureValuePair; this member field is
   * dynamically created during the initialization phase and is needed when
   * interfacing FSs to other components of a system;
   *
   * @see DagEdge
   * @see FeatureValuePair
   */
  protected ShortIDMap<String> featureIDMap;
  /**
   * reaction controls whether unknown feature/type names will be entered into
   * the above tables or not, and furthermore whether a warning will be printed;
   * possible values are: 1 = enter (default) 0 = warn and enter -1 = error
   */
  protected int reaction = 1;
  /**
   * this global is used by several predicates in order to check whether a given
   * type identifier is known or unknown
   */
  protected int noOfKnownTypes = 0;
  /**
   * this global is used by several predicates in order to check whether a given
   * feature identifier is new or already known
   */
  protected short noOfKnownFeatures = (short) 0;
  /**
   * assume that 0 represents <b>top</b>, the most general type of the type
   * hierarchy, denoting the universe of all feature structures
   */
  public static final int TOP_TYPE = 0;
  /**
   * assume that -1 represents <b>bottom</b>, the most specific type of the type
   * hierarchy, denoting the empty set (there will be no FS satisfying the
   * bottom type)
   */
  public static final int BOTTOM_TYPE = -1;
  public static final short ILLEGAL_FEATURE = -1;
  /**
   * in order to handle unknown string types, we need to know the name of the
   * string type (which is assumed to be the super type of these unknown types)
   */
  protected static String STRING_TYPE_NAME = "string";
  protected static String NULL_TYPE_NAME = "*null*";
  protected static String CONS_TYPE_NAME = "*cons*";
  protected static String QC_TYPE_NAME = "$qc_paths_set";
  protected static String FIRST_FEATURE_NAME = "CAR";
  protected static String REST_FEATURE_NAME = "CDR";
  protected static String ARGS_FEATURE_NAME = "DTRS";
  protected static String ATOM_STATUS_NAME = "*atom*";
  public static String RULE_STATUS_NAME = "rule";
  /** stores the type identifier (an int) for the string, cons and null type */
  protected int stringTypeID, consTypeID, nullTypeId;
  /** Cached codes of some features with special meanings */
  protected short firstFeatureId, restFeatureId, argsFeatureId;
  /** Cached code for the atom status */
  protected int atomStatusID;

  /**
   * types in the system are asssociated with a so-called status; a status is
   * abbreaviated by an int and the mapping from status numbers onto status
   * print names is encoded in the below instance field; possible status
   * mappings are: 0: *none* 1: *atom* 2: morph-template 3: c-lex-entry 4:
   * default-lex-entry 5: epsilon 6: lex-rule 7: root-node 8: sar-rule 9:
   * sar-root 10: lexroot 11: label 12: meta 13: rule 14: lex-entry
   */
  protected IntIDMap<String> status;

  /**
   * types in the system are asssociated with a so-called status; the mapping
   * from type id numbers (int) onto status numbers (int) is encoded in this
   * instance field; I use a hashtable (and NOT an array), since new types can
   * be introduced at run time
   */
  protected TIntIntHashMap typeNumber2StatusNumber;

  /**
   * offset from position zero, saying where the corresponding section starts in
   * randomAccessFile
   */
  protected int sectionOffsets[] = new int[Section.values().length];

  /**
   * an integer, representing the number of proper types, i.e., non-leaf types
   * in the type hierarchy;
   *
   * @see #isProperType
   */
  protected int noProperTypes;

  /**
   * an integer, representing the number of leaf types, i.e., non-proper types
   * in the type hierarchy; note that types lying on a chain, that starts from a
   * true leaf in the type hierarchy, are also regarded as leaf types;
   *
   * @see #isLeafType
   */
  protected int noLeafTypes;

  /**
   * this.noTypes = this.noProperTypes + this.noLeafTypes
   */
  protected int noTypes;

  /**
   * the instance field typeToBitcode encodes a mapping from proper type name
   * identifiers (ints) onto their codes (int arrays representing bit vectors);
   * note that gamma is a one-to- one mapping (an injection), and so we also
   * have an inverse mapping;
   *
   * @see #getGamma
   * @see #setGamma
   */
  protected int[][] typeToBitcode;

  /**
   * the inverse mapping to typeToBitCode, i.e., a mapping from codes
   * (int arrays) onto type name ids (ints); since not every index
   * (an int array) has a a corresponding type id, I use a hash table here to
   * establish bitCodeToType;
   *
   * @see #getGammaInv
   * @see #setGamma
   */
  protected TObjectIntHashMap<int[]> bitcodeToType;

  /** The super/subtype structure of the proper types */
  protected TIntArrayList[] parents, children;

  /**
   * the instance field delta encodes a mapping from leaf types (ints) in the
   * sense of PET onto proper parent type name identifiers (ints);
   *
   * @see #getLeafTypeParent
   * @see #setDelta
   */
  protected int[] leaftypeParent;

  /**
   * the instance field glbTable encodes a mapping from pairs of ints onto ints
   * and is a cache that is filled sucessively when type unification is called
   * at run time; the pair of ints represents the the arguments to type
   * unification, and the resulting integer represents the GLB;
   */
  protected TLongIntHashMap glbCache;

  /**
   * the mapping from type name identifiers (int) onto fully expanded, BUT
   * maximally unfilled feature structure objects;
   *
   * @see #phi
   * @see #getPi
   * @see #setPi
   * @see #getPhi
   * @see #setPhi
   */
  protected TFS[] pi;

  /**
   * the mapping from type name identifiers (int) onto fully expanded AND
   * totally filled feature structure objects;
   *
   * @see #pi
   * @see #getPhi
   * @see #setPhi
   * @see #getPi
   * @see #setPi
   */
  protected TFS[] phi;

  /** A very simple restrictor deleting all features mentioned here */
  protected TShortHashSet featuresToDelete = null;

  // BEGIN constructor

  /** Create an empty grammar. Currently only for the simple case where there
   *  are just atoms, and no real, pre-specified grammar
   */
  public FSGrammar() {
    typeNumber2StatusNumber = new TIntIntHashMap();
    status = new IntIDMap<String>();
    typeIDMap = new IntIDMap<String>();
    featureIDMap = new ShortIDMap<String>();

    atomStatusID = status.register(ATOM_STATUS_NAME);

    mapTypeToNumber("*TOP*");

    // finally assign the type number to the instance field stringType, used
    // during type unification and subsumption with unknown (string) types
    stringTypeID = mapTypeToNumber(STRING_TYPE_NAME);

    consTypeID = mapTypeToNumber(CONS_TYPE_NAME);
    nullTypeId = mapTypeToNumber(NULL_TYPE_NAME);

    firstFeatureId = mapFeatureToNumber(FIRST_FEATURE_NAME);
    restFeatureId = mapFeatureToNumber(REST_FEATURE_NAME);
    argsFeatureId = mapFeatureToNumber(ARGS_FEATURE_NAME);

    this.glbCache = new TLongIntHashMap();

    noProperTypes = 1; // only the TOP type is a proper type

    TFS.setGrammar(this);
  }


  /**
   * given a filename (which refers to the binary output of the flop
   * preprocessor of PET), ShUG() reads in (1) header (2) table of content (3)
   * symbol tables (4) type hierarchy (5) type constraints there exists a short
   * and partly outdated description of this binary representation in Uli
   * Callmeier's masters thesis
   *
   * @see "U. Callmeier: Efficient Parsing with Large-Scale Unification, Masters
   *      Thesis, Universitaet des Saarlandes, 2001"
   * @param filename
   *          the file name of a binary grm file that is produced by the PET
   *          preprocessor flop
   * @see AbstractGrammar
   */
  public FSGrammar(String filename) {
    // construct the global tables ...
    this(filename, defaultCharsetName, false);
  }

  /**
   * this constructor further prints out useful information during the
   * construction of this object by setting parameter printInfo to true
   */
  public FSGrammar(String filename, boolean printInfo) {
    this(filename, defaultCharsetName, printInfo);
  }

  /**
   * allows to directly further specify the character encoding
   */
  public FSGrammar(String filename, String chsetName) {
    this(filename, chsetName, false);
  }

  /**
   * this constructor further prints out useful information during the
   * construction of this object by setting parameter printInfo to true
   */
  public FSGrammar(String filename, String chsetName, boolean printInfo) {
    // could not use the this() notation to call the above constructor,
    // since it has to be the first statement, hence setting the encoding
    // afterwards is too late ...
    // now construct the global tables, ...
    super();
    // ... set the encoding, ...
    if (chsetName != null)
      this.charsetName = chsetName;
    if (Charset.isSupported(this.charsetName))
      this.charset = Charset.forName(this.charsetName);
    // ... and read in the binary file
    loadGrammar(filename);

    atomStatusID = status.getId(ATOM_STATUS_NAME);

    // finally assign the type number to the instance field stringType, used
    // during type unification and subsumption with unknown (string) types
    stringTypeID = getTypeId(STRING_TYPE_NAME);

    consTypeID = typeIDMap.getId(CONS_TYPE_NAME);
    nullTypeId = typeIDMap.getId(NULL_TYPE_NAME);

    firstFeatureId = featureIDMap.getId(FIRST_FEATURE_NAME);
    restFeatureId = featureIDMap.getId(REST_FEATURE_NAME);
    argsFeatureId = featureIDMap.getId(ARGS_FEATURE_NAME);

    if (printInfo)
      printSystemInfo();
    TFS.setGrammar(this);
  }

  /**
   * loadGrammar() is the helper for the two above constructors
   */
  public void loadGrammar(String filename) {
    long time = System.currentTimeMillis();
    // read in the binary file
    try {
      // now read the complete grm file into the byte array
      PetUndumper u = new PetUndumper();
      u.open(filename);
      // read header (some useful information), starting at position 0
      u.makeAbsoluteOffset(0);
      readHeader(u);
      // read table of content to determine the offsets,
      readTableOfContent(u);
      // read symbol tables for int-to-type/feature mappings;
      readSymbolTables(u);
      // read in the hierarchy,
      readHierarchy(u);
      // we are currently NOT interested in the feature tables (for fixed-arity
      // encoding)
      readFeatureTables(u);
      // we are currently NOT interested in the fullforms
      readSuperTypes(u);
      // i am VERY interested in the supertypes
      readFullforms(u);
      // we are currently NOT interested in inflection rules
      readInflectionRules(u);
      // we are currently NOT interested in the irregular morphological forms
      readIrregulars(u);
      // read in the constraints for proper and leaf types
      readConstraints(u);
      // and finally close the stream and free the memory
      u.close();
    } catch (IOException ioe) {
      LOGGER.error("Error while reading " + filename);
      System.exit(1);
    }
    LOGGER.info("overall load time: "
        + ((System.currentTimeMillis() - time) / 1000.0) + " secs\n");
  }

  /**
   * loadGrammar() is the helper for the two above constructors
   */
  public void loadChart(String filename, EdgeConsumer e) {
    long time = System.currentTimeMillis();
    // read in the binary file
    try {
      // now read the complete grm file into the byte array
      PetUndumper u = new PetUndumper();
      u.open(filename);
      // read header (some useful information), starting at position 0
      u.makeAbsoluteOffset(0);
      readHeader(u);
      // read table of content to determine the offsets,
      readTableOfContent(u);
      // read chart edges
      readChart(u, e);
      u.close();
    } catch (IOException ioe) {
      LOGGER.error("Error while reading " + filename);
      System.exit(1);
    }
    LOGGER.info("overall load time: "
        + ((System.currentTimeMillis() - time) / 1000.0) + " secs\n");
  }

  // END constructor

  // BEGIN getter/setter

  /**
   * returns system information
   */
  public StringBuffer getSystemInfo() {
    return this.allMessages;
  }

  /**
   * prints system information to logger
   */
  public void printSystemInfo() {
    FSGrammar.LOGGER.info(this.allMessages.toString());
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
  public void setCharEncoding(String chsetName) {
    this.charsetName = chsetName;
    if (Charset.isSupported(chsetName))
      this.charset = Charset.forName(chsetName);
  }

  // BEGIN getter/setter
  /** getTypeName() returns the type name associated with parameter index;
   * the null value is returned in case parameter index is not a legal type id
   */
  public String getTypeName(int index) {
    return this.typeIDMap.fromId(index);
  }
  /**
   * getNumberFromType() returns the integer associated with parameter typeName;
   * in case typeName is not a proper type name, BOTTOM_TYPE is returned
   */
  public int getTypeId(String typeName) {
    return (this.typeIDMap.contains(typeName) ?
        this.typeIDMap.getId(typeName) : BOTTOM_TYPE);
  }
  /**
   * getFeatureName() returns the feature name associated with parameter
   * index; it does not check whether parameter index is a proper feature index
   */
  public String getFeatureName(short index) {
    return this.featureIDMap.fromId(index);
  }
  /**
   * getNumberFromFeature() returns the short associated with parameter
   * featureName; in case featureName is not a proper feature name,
   * ILLEGAL_FEATURE is returned
   */
  public short getFeatureId(String featureName) {
    return this.featureIDMap.contains(featureName) ?
        this.featureIDMap.getId(featureName) : ILLEGAL_FEATURE;
  }
  /**
   * obtains the value that specifies the reaction in case of unknown types
   *
   * @see setReaction
   */
  public int getReaction() {
    return this.reaction;
  }
  /**
   * possible values are: 1 = enter (default) 0 = warn and enter -1 = error
   * otherwise, setReaction() results in an error
   */
  public void setReaction(int aReaction) {
    if ((aReaction == 1) || (aReaction == 0) || (aReaction == -1))
      this.reaction = aReaction;
    else {
      LOGGER.error("Wrong reaction value: " + aReaction
          + "; possible values are 1, 0, -1");
      System.exit(1);
    }
  }
  /**
   * given a feature name (a string), mapFeatureToNumber() obtains the
   * corresponding identifier (a short); in case that the feature name is
   * unknown to the system, mapFeatureToNumber() returns a new fresh short;
   * depending on the value of the instance field this.reaction, the reaction of
   * mapFeatureToNumber() can be controlled;
   *
   * @see setReaction
   */
  public short mapFeatureToNumber(String featureName) {
    if (! this.featureIDMap.contains(featureName)) {
      // no entry found
      if (this.reaction == -1) {
        LOGGER.error(featureName
            + " is not a proper feature name; exiting ...");
        System.exit(1);
      }
      if (this.reaction == 0)
        LOGGER.warn(featureName
            + " is not a proper feature name; entering it ...");
      // enter the mapping and its inverse
      return featureIDMap.register(featureName);
    }
    return this.featureIDMap.getId(featureName);
  }
  /**
   * given a type name (a string), mapTypeToNumber() obtains the corresponding
   * identifier (an int); in case that the type name is unknown to the system,
   * mapTypeToNumber() returns a new fresh int; depending on the value of the
   * instance field this.reaction, the reaction of mapTypeToNumber() can be
   * controlled;
   *
   * @see setReaction
   */
  private int mapTypeToNumberBasic(String typeName) {
    if (! this.typeIDMap.contains(typeName)) {
      // no entry found
      if (this.reaction == -1) {
        LOGGER.error(typeName
            + " is not a proper type name; exiting ...");
        System.exit(1);
      }
      if (this.reaction == 0)
        LOGGER.warn(typeName
            + " is not a proper type name; entering it ...");
      // enter the mapping and its inverse
      return typeIDMap.register(typeName);
    }
    return this.typeIDMap.getId(typeName);
  }
  /**
   * returns the number of types, known to the system (proper plus leaf types)
   */
  public int getNoOfKnownTypes() {
    return this.noOfKnownTypes;
  }

  public int getNoOfGrammarTypes() { return getNoOfKnownTypes(); }
  /**
   * tells the system how many types are known (proper plus leaf types)
   */
  public void setNoOfKnownTypes(int knownTypes) {
    this.noOfKnownTypes = knownTypes;
  }
  /**
   * returns the number of features, known to the system
   */
  public short getNoOfKnownFeatures() {
    return this.noOfKnownFeatures;
  }
  /**
   * tells the system how many features are known
   */
  public void setNoOfKnownFeatures(short knownFeatures) {
    this.noOfKnownFeatures = knownFeatures;
  }
  /**
   * @return true iff parameter typeIdent is equal to TOP_TYPE;
   *         false, otherwise
   */
  public boolean isTopType(int typeIdent) {
    return (typeIdent == TOP_TYPE);
  }
  /** @return true iff parameter typeIdent is equal to
   *          BOTTOM_TYPE; false, otherwise
   */
  public boolean isBottomType(int typeIdent) {
    return (typeIdent == BOTTOM_TYPE);
  }
  /** @return true iff parameter typeIdent is known to the system; false,
   *          otherwise
   */
  public boolean isGrammarType(int typeIdent) {
    return (typeIdent < this.noOfKnownTypes);
  }
  /** @return true iff parameter typeIdent is NOT known to the system; false,
   *          otherwise
   */
  public boolean isUnknownType(int typeIdent) {
    return (typeIdent >= this.noOfKnownTypes);
  }
  /** @return true iff parameter typeIdent currently a registered type, false
   *          otherwise
   */
  public boolean isType(String typeName) {
    return typeIDMap.contains(typeName);
  }

  /** getNoOfTypes() returns the number of currently represented types */
  public int getNoOfTypes() {
    return this.typeIDMap.size();
  }

  /** getNoOfFeatures() returns the number of currently represented features */
  public short getNoOfFeatures() {
    // size() returns an int, so (short)en it
    return (short) this.featureIDMap.size();
  }

  /** obtains the status print name for the given int; does not check whether
   *  parameter index is a valid status name identifier;
   * @see #number2Status
   */
  public String getStatusName(int index) {
    return this.status.fromId(index);
  }

  /** get the status id from its name */
  public int getStatusID(String name) {
    return this.status.getId(name);
  }

  /** obtains the status name identifier for type id
   * @see #typeNumber2StatusNumber
   */
  public int getStatusForType(int typeNo) {
    return this.typeNumber2StatusNumber.get(typeNo);
  }

  /** return the type ids for all types marked with RULE_STATUS */
  public List<Integer> getRuleTypes() {
    List<Integer> result = new ArrayList<Integer>();
    int ruleStatus = getStatusID(RULE_STATUS_NAME);
    for(int type = 0; type < getNoOfKnownTypes(); ++type) {
      if (getStatusForType(type) == ruleStatus) {
        result.add(type);
      }
    }
    return result;
  }

  /**
   * given a type name (a string), mapTypeToNumber() obtains the corresponding
   * identifier (an int); in case that the type name is unknown to the system,
   * mapTypeToNumber() returns a new fresh int; note that I extend (by
   * overwriting) the functionality of mapTypeToNumber() from superclass
   * AbstractGrammar in that a new unknown type is assigned an atom status (int
   * value = 1)
   */
  public int mapTypeToNumber(String typeName) {
    // obtain the type id for the type name
    int typeNo = mapTypeToNumberBasic(typeName);
    // check whether typeNo is an unknown (currently introduced new) type;
    if (isUnknownType(typeNo))
      // if so, assign ShUG.ATOM_STATUS_NUMBER as the status value for this type
      typeNumber2StatusNumber.put(typeNo, atomStatusID);
    return typeNo;
  }
  public int getNumberForTypeName(String typeName)  {
    return mapTypeToNumber(typeName);
  }
  /**
   * given a typeNo (an int), getAtomName() returns the name (a string) for
   * typeNo iff typeNo represents an atom; otherwise null is returned (= a
   * known, non-atom type)
   */
  public String getAtomName(int typeNo) {
    if (getStatusForType(typeNo) == atomStatusID)
      return getTypeName(typeNo);
    return null;
  }

  /**
   * getGamma() obtains the type hierarchy code (an int array representing a bit
   * vector) for a given proper type name identifier (an int); note that I do
   * NOT check whether parameter propTypeIdent is in fact a proper type name id,
   * i.e., whether propTypeIdent < this.noProperTypes
   *
   * @see #typeToBitcode
   */
  public int[] getBitcodeForType(int propTypeIdent) {
    if (propTypeIdent == BOTTOM_TYPE)
      // I always return the same int vector for the bottom type
      return this.bottomCode;

    return this.typeToBitcode[propTypeIdent];
  }

  /**
   * setGamma() establishes a two-way mapping between proper type name
   * identifiers and their codes; note that I do NOT check whether
   * propTypeIdent < this.gamma.length
   *
   * @see #typeToBitcode
   */
  private void setBitcodeForType(int propTypeIdent, int[] code) {
    this.typeToBitcode[propTypeIdent] = code;
    // since hashtable neither allow keys nor values to be primitive data, we
    // must convert the code to a codeVector and the type identifier into an
    // Int object
    this.bitcodeToType.put(code, propTypeIdent);
  }

  /**
   * isBottomCode() checks whether a given type hierarchy code (an int array) is
   * (structural) equivalent to the bottom code vector (usually a sequence of
   * int zeros);
   *
   * @see #bottomCode
   */
  public boolean isBottomCode(int[] code) {
    // all code vectors have the same length
    for (int i = 0; i < code.length; i++) {
      if (code[i] != 0)
        return false;
    }
    return true;
  }

  /**
   * given an int vector (representing a bit code), getGammaInv() returns the
   * type identifier (an int) for this code; note that getGammaInv() does NOT
   * check whether there exists a type identifier for a given code
   */
  public int getGammaInv(int[] code) {
    // since hashtable neither allow keys nor values to be primitive data,
    // we must convert the code into a CodeVector object and the Int result
    // into an int
    if (isBottomCode(code))
      return BOTTOM_TYPE;

    return this.bitcodeToType.get(code);
  }


  /**
   * given a leaf type identifier, getDelta() returns the direct parent type
   * identifier, either a proper type or again a leaf type (in the terminology
   * of PET)
   */
  public int getLeafTypeParent(int leafTypeIdent) {
    if (! isGrammarType(leafTypeIdent)) return TOP_TYPE;
    // note that the parameter leafTypeIdent >= this.noProperTypes, hence we
    // must map leafTypeIdent to the right index in the delta array, since it
    // starts with index 0:
    // leafTypeIdent - this.noProperTypes
    return leaftypeParent[leafTypeIdent - this.noProperTypes];
  }

  /**
   * setDelta() establishes a mapping between a leaf type identifier and its
   * direct parent type id, either a proper type or again a leaf type (in the
   * terminology of PET)
   */
  private void setDelta(int leafTypeIdent, int parentTypeIdent) {
    // the value of the parameter leafTypeIdent must actually be read as
    // leafTypeIdent + this.noProperTypes
    // but since Java arrays start at position 0, we assign the first leaf
    // type the index 0 in the delta array
    this.leaftypeParent[leafTypeIdent] = parentTypeIdent;
  }

  /**
   * since the codes are int vectors, code unification reduces to a pairwise bitwise
   * AND & on the integers
   * @return a new codevector, representing the bitwise AND of the code of this object
   *         and parameter arg
   */
  public static int[] unifyCodes(int[] thisCode, int[] argCode) {
    // we assume that this object and parameter arg are of the same length
    int thisLength = thisCode.length;
    int[] resultCode = new int[thisLength];
    for (int i = 0; i < thisLength; i++)
      resultCode[i] = thisCode[i] & argCode[i];
    return resultCode;
  }

  /**
   * since the codes are int vectors, code generalization reduces to a pairwise bitwise
   * OR | on the integers
   * @return a new codevector, representing the bitwise OR of the code of this object
   *         and parameter arg
   */
  public static int[] generalizeCodes(int[] thisCode, int[] argCode) {
    // we assume that this object and parameter arg are of the same length
    int thisLength = thisCode.length;
    int[] resultCode = new int[thisLength];
    for (int i = 0; i < thisLength; i++)
      resultCode[i] = thisCode[i] | argCode[i];
    return resultCode;
  }

  /**
   * since the codes are int vectors, code subsumption reduces to a pairwise test
   * whether the bits of parameter arg are set in object this; we can express this
   * by employing bitwise AND &:  arg <= this  :<==>  arg & this == arg
   * @return true iff the code for this object subsumes (is more general than) the
   *         code of parameter arg; false otherwise
   */
  public static boolean subsumesCode(int[] thisCode, int[] argCode) {
    // we assume that this object and parameter arg are of the same length
    for (int i = 0; i < thisCode.length; i++) {
    if ((argCode[i] & thisCode[i]) != argCode[i])
      return false;
    }
    return true;
  }

  /**
   * @param typeIdent1
   *          the type identifier (an int) for type1
   * @param typeIdent2
   *          the type identifier (an int) for type2
   * @return an int, representing the type identifier for the GLB of type1 and
   *         type2; there exist special return values, representing the TOP type
   *         and the BOTTOM type, but also a currently not computed GLB for
   *         type1 and type2:
   * @see AbstractGrammar#TOP_TYPE (usually 0)
   * @see AbstractGrammar#BOTTOM_TYPE (usually -1)
   * @see #GLB_NOT_COMPUTED (usually -2) these protected fields are encapsulted
   *      in three boolean getters (test methods):
   * @see #isTopType
   * @see #isBottomType
   * @see #glbIsCached
   */

  /**
   * given a type identifier (an int), getPi() returns the globally expanded,
   * BUT unfilled prototypical feature structure (but NOT a copy of it);
   *
   * @see #getPrototype to obtain a copied prototype
   */
  public TFS getPi(int typeIdent) {
    if (typeIdent == BOTTOM_TYPE) return null;
    // distinguishes between types introduced via the binary grm images and
    // unknown types,
    // introduced at run time
    if (typeIdent < this.noTypes)
      return this.pi[typeIdent];

    // atomic types are ALWAYS maximally unfilled
    return new TFS(typeIdent);
  }

  /**
   * given a type name (a string), getPi() returns the globally expanded, BUT
   * unfilled prototypical feature structure (but NOT a copy of it);
   *
   * @see #getPrototype to obtain a copied prototype
   */
  public TFS getPi(String typeName) {
    return getPi(getTypeId(typeName));
  }

  public TFS getFS(int typeIdent) { return getPi(typeIdent); }
  public TFS getFS(String typeIdent) { return getPi(typeIdent); }

  /**
   * setPi() establishes an association between a type identifier (an int) and
   * its globally expanded (but unfilled) prototypical feature structure; note
   * that typeIdent < this.noTypes must be the case
   */
  protected void setPi(int typeIdent, TFS fs) {
    this.pi[typeIdent] = fs;
  }

  /**
   * given a type identifier (an int), getPhi() returns the globally expanded
   * AND totally filled prototypical feature structure (but NOT a copy of it);
   * note that the null value is returned in case that NO filled structure is
   * currently available;
   *
   * @see #fillFS() to compute a filled FS
   */
  public TFS getPhi(int typeIdent) {
    // distinguishes between types introduced via the binary grm images and
    // unknown types,
    // introduced at run time
    if (typeIdent < this.noTypes)
      return this.phi[typeIdent];

    // atomic types are ALWAYS totally filled
    return new TFS(typeIdent);
  }

  /**
   * given a type name (a string), getPhi() returns the globally expanded AND
   * totally filled prototypical feature structure (but NOT a copy of it); note
   * that the null value is returned in case that NO filled structure is
   * currently available;
   *
   * @see #fillFS() to compute a filled FS
   */
  public TFS getPhi(String typeName) {
    return getPhi(getTypeId(typeName));
  }

  /**
   * setPhi() establishes an association between a type identifier (an int) and
   * its globally expanded AND totally filled prototypical feature structure;
   * note that typeIdent < this.noTypes must be the case---this is NOT checked
   * by setPhi()
   */
  protected void setPhi(int typeIdent, TFS fs) {
    this.phi[typeIdent] = fs;
  }

  /**
   * given a type identifier (an int), getPrototype() returns a copy of the
   * globally expanded (but unfilled) prototypical feature structure; we always
   * copy the prototypes, since we want the data base (aka the grammar) to be
   * untouched;
   *
   * @see #getPi to obtain a non-copied prototype
   */
  public TFS getPrototype(int typeIdent) {
    return getPi(typeIdent).cloneFS();
  }

  /**
   * given a type name (a string), getPrototype() returns a copy of the globally
   * expanded (but unfilled) prototypical feature structure; we always copy the
   * prototypes, since we want the data base (aka the grammar) to be untouched
   *
   * @see #getPi to obtain a non-copied prototype
   */
  public TFS getPrototype(String typeName) {
    return getPi(typeName).cloneFS();
  }

  private void clearSectionOffsets() {
    Arrays.fill(sectionOffsets, -1);
  }

  private void setSectionOffset(Section s, int offset) {
    sectionOffsets[s.ordinal()] = offset;
  }

  private int getSectionOffset(Section s) {
    return sectionOffsets[s.ordinal()];
  }

  // END getter/setter


  // BEGIN reader

  /**
   * some very uninteresting information for us (at the moment) we have to skip
   * over
   */
  private void readHeader(PetUndumper u) {
    // magic value to identify file format
    u.undumpInt();
    // version of file format
    u.undumpInt();
    // description (name) of the grammar
    allMessages.append("reading header: " + u.undumpString() + " ...\n");
  }

  /**
   * the TOC consists of a sequence of pairs of integers; each pair describes a
   * section, the first element denotes the section type, whereas the second
   * represents the offset of the beginning of this section into the file; the
   * end of the TOC is indicated by section type 0, followed by no offset; there
   * will be no fix order of the sections after the TOC; there might even be
   * unknown sections; the encoding of the actual sections is as follows: 0 =
   * SEC_NOSECTION 1 = SEC_SYMTAB 2 = SEC_PRINTNAMES 3 = SEC_HIERARCHY 4 =
   * SEC_FEATTABS 5 = SEC_FULLFORMS 6 = SEC_INFLR 7 = SEC_CONSTRAINTS 8 =
   * SEC_IRREGS >=9 = unknown sections at the moment
   */
  private void readTableOfContent(PetUndumper u) {
    allMessages.append("reading table of content ...\n");
    clearSectionOffsets();
    int sectionType;
    // 0 indicates the end of TOC
    while ((sectionType = u.undumpInt()) != 0) {
      // don't know if section types come in ascending order
      if (sectionType > 0 && sectionType < Section.values().length) {
        setSectionOffset(Section.values()[sectionType], u.undumpInt());
      } else {
        LOGGER.warn ("unknown section type: " + sectionType + "\n");
        u.undumpInt();
        break;
      }
    }
  }

  /**
   * note that the original documentation for the symbol tables is NO longer
   * valid; the sequence is now as follows: int | section type (always = 1) int
   * | nstatus int | npropertypes int | nleaftypes int | nattrs nstatus x string
   * | status names (npropertypes + nleaftypes) x (string + int) | type names &
   * type status nattrs x string | feature name note further that
   * readSymbolTables() also establishes a mapping between the string type name
   * and the string type identifier
   */
  private void readSymbolTables(PetUndumper u) {
    int noAttributes, noStatus;
    allMessages.append("reading symbol tables ...\n");
    // move to the right position
    u.makeAbsoluteOffset(getSectionOffset(Section.SYMTAB));
    // read off the important numbers:
    u.undumpInt(); // = 1 = section type
    allMessages.append("  # status: " + (noStatus = u.undumpInt()) + "\n");
    allMessages.append("  # proper types: "
        + (this.noProperTypes = u.undumpInt()) + "\n");
    allMessages.append("  # leaf types: " + (this.noLeafTypes = u.undumpInt())
        + "\n");
    allMessages
        .append("  # attributes: " + (noAttributes = u.undumpInt()) + "\n");
    // create the missing tables
    this.noTypes = this.noProperTypes + this.noLeafTypes;
    this.status = new IntIDMap<String>(noStatus);
    this.typeNumber2StatusNumber = new TIntIntHashMap(this.noTypes);
    // read in the status/type/feature tables
    String string;
    int statID;
    // establish a mapping from ints onto status names
    for (int i = 0; i < noStatus; i++)
      status.register(u.undumpString());
    // say how many types we know beforehand
    setNoOfKnownTypes(this.noTypes);
    // establish the type mapping
    typeIDMap = new IntIDMap<String>(this.noTypes);
    for (int i = 0; i < this.noTypes; i++) {
      string = u.undumpString();
      int newID = typeIDMap.register(string); assert(newID == i);
      statID = u.undumpInt();
      typeNumber2StatusNumber.put(i, statID); // status (int) of type (int)
    }
    // say how many features we know beforehand
    setNoOfKnownFeatures((short) noAttributes);
    // establish the feature mapping
    featureIDMap = new ShortIDMap<String>(noAttributes);
    for (short i = (short) 0; i < noAttributes; i++) {
      string = u.undumpString();
      int newID = featureIDMap.register(string); assert(newID == i);
    }
  }

  /**
   * the hierarchy section starts with the section type number (= 3), followed
   * by the number of bits (an int) needed for (compact-)encoding the type
   * hierarchy of the proper types; we then read in the codes for the proper
   * types, realized as vectors of ints (and NOT of bytes); the encoding is done
   * by undumpBitcode(); the mapping between proper type identifiers (ints) and
   * codes (int vecors) is established by gamma (an int[][] array); there also
   * exists an inverse mapping called gammaInverse; finally, we build up an
   * association between leaf type identifiers (ints) and parent type
   * identifiers (ints)
   *
   * @see #undumpBitcode
   */
  @SuppressWarnings("serial")
  private void readHierarchy(PetUndumper u) {
    allMessages.append("reading type hierarchy ...\n");
    // move to the right position
    u.makeAbsoluteOffset(getSectionOffset(Section.HIERARCHY));
    u.undumpInt(); // = 3 = section type
    int noOfBits = u.undumpInt();
    allMessages.append("  code length (# bits): " + noOfBits + "\n");
    // compute the number of ints for encoding the proper types
    int codesize = (noOfBits / FSGrammar.INT_SIZE) + 1;
    // Java guarantees that the values held in a new int array are zeros and
    // exactly
    // the zero-vector is the code for the bottom type, thus no initialization
    this.bottomCode = new int[codesize];
    // create gamma, the mapping from type identifiers (ints) onto codes (int
    // array),
    this.typeToBitcode = new int[this.noProperTypes][codesize];
    // ... but also the inverse mapping
    this.bitcodeToType = new TObjectIntHashMap<int[]>(this.noProperTypes,
            new TObjectHashingStrategy<int[]>() {
              public static final int BITS_PER_INT = 32;

              public int computeHashCode(int[] arg0) {
                int i = 0;
                while(i < arg0.length && arg0[i] == 0) { ++i; }
                return (i * BITS_PER_INT)
                        + Integer.numberOfTrailingZeros(arg0[i]);
              }

              public boolean equals(int[] arg0, int[] arg1) {
                int i = arg0.length - 1;
                while (i > 0 && (arg0[i] == arg1[i])) { --i; }
                return arg0[i] == arg1[i];
              }

            });
    int i;
    int[] code;
    // read in the code vector for the proper types
    for (i = 0; i < this.noProperTypes; i++) {
      code = u.undumpBitcode(codesize);
      setBitcodeForType(i, code);
    }
    // establish a mapping delta from leaf types (int) onto proper parent types
    // (int);
    // in order to obtain the right parent number for a leaf, one has to
    // substract
    // from the leaf number the global instance field noProperTypes
    this.leaftypeParent = new int[this.noLeafTypes];
    for (i = 0; i < this.noLeafTypes; i++)
      setDelta(i, u.undumpInt());
    // finally create the cache (a hashtable) for the GLBs
    this.glbCache = new TLongIntHashMap();
  }

  /**
   * the body of readFeatureTables() is currently empty, since this information
   * is at the moment NOT relevant for ShUG/SProUT
   * @param u the undumper to read from
   */
  private void readFeatureTables(PetUndumper u) {
    // nothing to do here
  }

  /**
   * The immediate supertypes for every type.
   * @param u the undumper to read from
   */
  private void readSuperTypes(PetUndumper u) {
    this.parents = new TIntArrayList[this.noProperTypes];
    this.children = new TIntArrayList[this.noProperTypes];
    allMessages.append("reading supertype structure ...\n");
    // move to the right position
    u.makeAbsoluteOffset(getSectionOffset(Section.SUPERTYPES));
    u.undumpInt(); // == section type
    for(int i = 0; i < this.noProperTypes; ++i) {
      short noSuperTypes = u.undumpShort();
      this.parents[i] = new TIntArrayList(noSuperTypes);
      for (short s = 0; s < noSuperTypes; ++s) {
        int parent = u.undumpInt();
        this.parents[i].add(parent);
        if (this.children[parent] == null)
          this.children[parent] = new TIntArrayList(5);
        this.children[parent].add(i);
      }
    }
  }

  /**
   * the body of readFullforms() is currently empty, since this information, if
   * present at all, is at the moment NOT relevant for ShUG/SProUT
   * @param u the undumper to read from
   */
  private void readFullforms(PetUndumper u) {
    // nothing to do here
  }

  /**
   * the body of readInflectionRules() is currently empty, since this
   * information, if present at all, is at the moment NOT relevant for
   * ShUG/SProUT
   * @param u the undumper to read from
   */
  private void readInflectionRules(PetUndumper u) {
    // nothing to do here
  }

  /**
   * the body of readInflectionRules() is currently empty, since this
   * information, if present at all, is at the moment NOT relevant for
   * ShUG/SProUT
   * @param u the undumper to read from
   */
  private void readIrregulars(PetUndumper u) {
    // nothing to do here
  }

  /**
   * readConstraints() read in the constraints (= fully expanded, but unfilled
   * feature structures), both for the proper and the leaf types; for a given
   * type (ident) to be constructed, every feature structure (incl. the top
   * structure) as well as every feature-value pair is assigned an index and can
   * be accessed through the global arrays this.featureStructures and
   * this.featureValuePair; these arrays are build up for every type that is
   * read in; constraint: int | nnodes int | narcs nnodes x node | node node:
   * int | type short | nattrs nattrs x arc | arc arc: short | attribute short |
   * value
   * @param u the unduper to read from
   *
   * @see #undumpNode
   * @see #undumpArc
   */
  private void readConstraints(PetUndumper u) {
    int totalNoNodes = 0, totalNoArcs = 0;
    allMessages.append("reading constraints ...\n");
    // move to the right position
    u.makeAbsoluteOffset(getSectionOffset(Section.CONSTRAINTS));
    // create the ident-2-FS table
    allMessages.append("  # expanded, unfilled types: " + this.noTypes + "\n");
    this.pi = new TFS[this.noTypes];
    this.phi = new TFS[this.noTypes];
    u.undumpInt(); // = 7 = section type
    int i = 0 ;
    // successively read in the dumped FSs
    while (i < this.noTypes) {
      // now make the association between type ident i and constructed FS (last
      // position in node array)
      setPi(i, TFS.buildFS(u));
      i++;
    }
    allMessages.append("  # created nodes: " + totalNoNodes + "\n");
    allMessages.append("  # created arcs: " + totalNoArcs + "\n");
  }


  /** Read chart edges dumped in binary format:
   *  <int> id start end
   *  <string> name
   *  <short> arity <int> dtrs-id^arity
   *  <dag> dag
   * @param filename
   * @param e
   */
  private void readChart(PetUndumper u, EdgeConsumer e) {

    //LOGGER.info("reading chart ...\n");
    // move to the right position
    int offs = getSectionOffset(Section.CHART);
    u.makeAbsoluteOffset(offs);
    // undump section type
    int sType = u.undumpInt();
    assert(sType == Section.CHART.ordinal());
    // read the chart size
    int start = u.undumpInt();
    int end = u.undumpInt();
    e.setChartSize(end - start);

    // read the edges
    while (true) {
      int id = u.undumpInt();
      start = u.undumpInt();
      end = u.undumpInt();
      if (id == 0 && start == 0 && end == 0) break;
      String name = u.undumpString();
      short arity = u.undumpShort();
      ArrayList<Integer> dtrs = new ArrayList<Integer>(arity);
      for (short s = 0; s < arity; ++s) {
        dtrs.add(u.undumpInt());
      }
      TFS fs = TFS.buildFS(u);
      e.addEdge(id, start, end, name, dtrs, fs);
    }
  }

  // END reader

  // BEGIN type unification/subsumption/filling

  /**
   * @return true iff value of parameter typeIdent is a proper type; false,
   *         otherwise
   */
  public boolean isProperType(int typeIdent) {
    return (typeIdent < this.noProperTypes);
  }

  /**
   * @return true iff value of parameter typeIdent is a leaf type; false,
   *         otherwise
   */
  public boolean isLeafType(int typeIdent) {
    return (typeIdent >= this.noProperTypes);
  }


  /** return true if t1 is subtype of t2 */
  protected boolean subType(int t1, int t2) {
    if (t1 == t2) return true;
    if (t2 == TOP_TYPE) return true;

    if (t1 == BOTTOM_TYPE) return true;
    if (t2 == BOTTOM_TYPE) return false;

    if (isLeafType(t1))
      return subType(getLeafTypeParent(t1), t2);

    // t1 is not a leaf type:
    // return true if the code vector for t2 is more general than for t1
    return subsumesCode(getBitcodeForType(t2), getBitcodeForType(t1));
  }

  protected boolean subTypeBothLeafTypes(int t1, int t2) {
    if (t1 == t2) return true;
    if (isLeafType(t1))
      return subTypeBothLeafTypes(getLeafTypeParent(t1), t2);
    return false;
  }

  /**
   * unifyTypes() takes two type identifiers (ints) and returns the identifier
   * (again an int) for the GLB
   */
  public int unifyTypes(int t1, int t2) {
    // swap the parameter value in order to guarantee that
    // typeIdent1 <= typeIdent2 is ALWAYS the case;
    if (t1 > t2) {
      int buffer = t1;
      t1 = t2;
      t2 = buffer;
    }

    // not every configuration is recorded to reduce the size of the table
    // TOP case and '==' case
    if (t1 == TOP_TYPE || t1 == t2)
      return t2;

    // typeIdent2 may not be TOP_TYPE) since TOP has the
    // smallest ident and tI1 <= tI2

    // now obtain the (unique long) integer code for the GLB of tI1 and tI2
    long idx = t2 + this.noTypes * t1;
    if (glbCache.containsKey(idx))
      return glbCache.get(idx);

    int result = BOTTOM_TYPE;
    // now distinguish between proper types and leaf types, since only
    // proper types have a gamma value;
    // are both type identifiers leaf types (hope this is the most
    // frequently chosen case, besides caching)?
    if (isLeafType(t1)) {
      if (isLeafType(t2)) {
        if (subTypeBothLeafTypes(t1, t2))
          result = t1;
        else if (subTypeBothLeafTypes(t2, t1))
          result = t2;
      } else if (subType(t1, t2))
        result = t1;
    } else {
      // typeIdent1 has to be a proper type by now
      if (isLeafType(t2)) {
        if (subType(t2, t1))
          result = t2;
      } else {
        // now either typeIdent1 or typeIdent2 is a leaf type, or both are
        // proper types; determine the bit/integer code for the leaf type by
        // using the parent code of the minimal proper type
        // both types are proper types, but are currently not cached

        // since the type hierarchy is a BCPO (or equivalently, a LSL), the
        // inverse image of gamma is guaranteed to exist
        result = getGammaInv(unifyCodes(getBitcodeForType(t2),
            getBitcodeForType(t1)));
      }
    }

    this.glbCache.put(idx, result);
    return result;
  }

  /**
   * does typeIdent1 subsumes (is more general than or equal to) typeIdent2, i.e.
   * is typeIdent1 a supertype of typeIdent2
   */
  public boolean subsumesType(int typeIdent1, int typeIdent2) {
    return unifyTypes(typeIdent1, typeIdent2) == typeIdent2;
  }

  /**
   * --- TO BE IMPLEMENTED ---
   *
   * @throws UnsupportedOperationException
   */
  public int generalizeTypes(int type1, int type2) {
    throw new UnsupportedOperationException(
        "generalizeTypes() is NOT implemented for class ShUG");
  }

  // TODO: Move this into DagNode/TFS
  /**
   * fillFS1() destructively does the recursive work for fillFS();
   *
  private void fillFS1(TFS fs) throws UnificationFailureException {
    // is the FS bag a feature structure or an FS set

    int typeId = fs.getType();
    // only if typeId is a known non-atom type, we have to recursively fill the
    // FS;
    // otherwise, nothing needs to be done, since the FS represents an atom;
    // note that UNKNOWN types, introduced at run time, are always assumed to be
    // atoms,
    // viz., strings
    if (isKnownType(typeId) && (getAtomName(typeId) == null)) {
      TFS phiFs = getPhi(typeId);
      if (phiFs == null) {
        // there is NO globally expanded and totally filled FS for typeId, thus
        // create such
        // a structure by applying fillFS() to the global prototype of typeId
        // and CACHE the
        // result;
        // this should never fail, since the original filled global prototype
        // was successful
        // before it gets unfilled
        phiFs = fillFS(getPrototype(typeId));
        // anyway, make the test
        if (phiFs == null)
          // failure during filling is due to a unification failure;
          // types are already encapsulted in the exception object
          throw FSGrammar.FAILURE;
        // otherwise store phiFs, since it might be used inside the recursive
        // call to fillFS()
        setPhi(typeId, phiFs);
      }
      // since we destructively work on fs, I make a copy of phiFs here to
      // obviate the call
      // to invalidateEffects(); we use phiFs later
      phiFs = phiFs.copyFS();
      // now iterate over the FV pairs, applying fillFS() to the values;
      // note that we destructively work on the values to retain the right
      // coreference
      // bindings across the whole structure
      ArrayList<DagNode.DagEdge> fvPairs = fs.getFeatureValueList();
      for (int i = 0; i < fvPairs.size(); i++)
        fillFS1(fvPairs.get(i).getValue().derefFS());
      // finally unify the filled FS for typeId (= phiFs) with the filled input
      // argument (= fs);
      // I apply this unification at last, since there is no need to apply
      // fillFS() to the
      // filled structure, coming solely from typeId (it is filled and already
      // copied!)
      fs = fs.unifyFS(phiFs);
      // was unification successful (nothing to be done, since fillFS()
      // destructively works on fs);
      // should usually be the case, assuming the below conditions in header of
      // fillFS() do hold;
      // but nevertheless I make a test here
      if (fs == null)
        // failure types are already encapsulted in the exception object
        throw FSGrammar.FAILURE;
    }
  }

  /**
   * given an FS bag fs, fillFS() DESTRUCTIVELY fills argument fs; assuming that
   * fs is maximally expanded, fillFS() extends fs in that it becomes most
   * specific according to all its supertypes and its idiosyncratic feature
   * constraints, specified in its type definition; fillFS() should never fail
   * (aka unification failure), ASSUMING that the feature structures are
   * well-typed and their types regard the corresponding approriateness
   * conditions; note that fillFS() always derefs its argument FS bag;
   *
   * @return the filled FS bag or null in case of a unification failure (in case
   *         that the above assumption does NOT hold)
   *
  public TFS fillFS(TFS fs) {
    try {
      fillFS1(fs); // fillFS1() destructively modifies fs
    } catch (UnificationFailureException ufe) {
      return null;
    }
    return fs;
  }
  */

  /**
   *
   * @return -1 the type is (at the moment) not defined in the type hierarchy
   * @return 0 the type is defined in the type hierarchy and either the feature
   *         is not specified, or not appropriate, or a totally unknown feature
   * @return 1 the type is defined in the type hierarchy and the feature is
   *         appropriate
   */
  public int featureIsAppropriate(String typeName, String featureName) {
    if (! isType(typeName))
      // type not known to ShUG
      return -1;
    if (featureName == null)
      // type exists, but no feature is specified for appropriateness check
      return 0;
    short featureNo = getFeatureId(featureName);
    if (featureNo == -1)
      // type exists, but feature is unknown to ShUG
      return 0;
    // obtain the FS with name typeName (quite similar to TDL's global prototype
    // modulo unfilling)
    TFS fs = getPi(getTypeId(typeName));
    DagEdge fvp;
    Iterator<? extends DagEdge> fvList = fs.dag().getEdgeIterator();
    while(fvList.hasNext()) {
      fvp = fvList.next();
      if (fvp.getFeature() == featureNo)
        return 1;
    }
    // type exists, but feature not found in the feature-value list of FS fs
    return 0;
  }

  /** Check if this feature should remain in the structure during jxchg reading
   *
   * @param featval
   * @return true if the feature should remain in the structure
   */
  public boolean keepFeature(short featval) {
    if (featuresToDelete == null) return true;
    return ! featuresToDelete.contains(featval);
  }

  /** Add a feature name to delete from the jxchg structures */
  public void addFeatureToDelete(String name) {
    short feature = getFeatureId(name);
    if (feature != ILLEGAL_FEATURE) {
      if (featuresToDelete == null) {
        featuresToDelete = new TShortHashSet();
      }
      featuresToDelete.add(feature);
    }
  }

  /** Add a feature name to delete from the jxchg structures */
  public void clearFeaturesToDelete() {
    if (featuresToDelete != null)
      featuresToDelete.clear();
  }

  // END type unification/subsumption/filling

  /** read the specified (possibly compressed) jxchg files and put the
   * feature structures into an array list.
   */
  public void
  readTFSFile(File file, EdgeConsumer consumer) {
    Reader in = null;
    try {
      if (file.getName().endsWith(".gz")) {
        in = new InputStreamReader(
               new GZIPInputStream(new FileInputStream(file)));
      } else {
        in = new FileReader(file);
      }
      JxchgTokenizer tok = new JxchgTokenizer(new BufferedReader(in));
      tok.readEdges(consumer);
      in.close();
    } catch (FileNotFoundException fnfex) {
      LOGGER.warn(fnfex.getMessage());
    } catch (IOException ioex) {
      LOGGER.warn(ioex.getMessage());
    } catch (InvalidSyntaxException isex) {
      File moveTo =
        new File(file.getParent() + File.separator + "bad" + File.separator
            + file.getName());
      boolean moved = file.renameTo(moveTo);
      LOGGER.warn(isex.getMessage() + " in " + file
          + " was " + (moved ? "" : "not ") +  "moved to `bad' ");
    }
  }

  public void readTFSFile(String fileName, EdgeConsumer consumer) {
    readTFSFile(new File(fileName), consumer);
  }

  /** read the specified (possibly compressed) jxchg files and put the
   * feature structures into an array list.
   */
  public void
  readTFSFiles(Iterator<String> fileNames, EdgeConsumer consumer, int maxAdded){
    if (! fileNames.hasNext())
      throw new IllegalArgumentException("No filename given");
    String firstFile = fileNames.next();
    File f = new File(firstFile);
    if (f.isDirectory()) {
      String[] files = f.list();
      for (int i = 0; (i < files.length &&
                       (maxAdded == 0 || consumer.added() <= maxAdded)); ++i) {
        readTFSFile(new File(f, files[i]), consumer);
      }
    } else {
      readTFSFile(firstFile, consumer);
      while (fileNames.hasNext() &&
          (maxAdded == 0 || consumer.added() <= maxAdded)) {
        readTFSFile(fileNames.next(), consumer);
      }
    }
  }

  public short getArgsFeature() {
    return argsFeatureId;
  }

  public short getFirstFeature() {
    return firstFeatureId;
  }

  public short getRestFeature() {
    return restFeatureId;
  }

  public int getConsType() {
    return consTypeID;
  }

  public int getNullType() {
    return nullTypeId;
  }

  public TFS getQCDag() {
    return (isType(QC_TYPE_NAME) ? getPi(QC_TYPE_NAME) : null);
  }

  TIntArrayList getParents(int type) {
    if (isLeafType(type)) {
      TIntArrayList result = new TIntArrayList(1);
      result.add(getLeafTypeParent(type));
      return result;
    }
    return parents[type];
  }

}
