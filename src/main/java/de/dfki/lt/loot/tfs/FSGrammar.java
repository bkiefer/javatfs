package de.dfki.lt.loot.tfs;

import gnu.trove.list.array.TIntArrayList;
import gnu.trove.map.TIntIntMap;
import gnu.trove.map.TLongIntMap;
import gnu.trove.map.custom_hash.TObjectIntCustomHashMap;
import gnu.trove.map.hash.TIntIntHashMap;
import gnu.trove.map.hash.TLongIntHashMap;
import gnu.trove.procedure.TIntIntProcedure;
import gnu.trove.procedure.TLongIntProcedure;
import gnu.trove.set.hash.TShortHashSet;
import gnu.trove.strategy.HashingStrategy;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.Reader;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import org.apache.log4j.Logger;

import de.dfki.lt.loot.tfs.io.Consumer;
import de.dfki.lt.loot.tfs.io.EdgeConsumer;
import de.dfki.lt.loot.tfs.io.InvalidSyntaxException;
import de.dfki.lt.loot.tfs.io.JxchgTokenizer;
import de.dfki.lt.loot.tfs.io.PetUndumper;
import de.dfki.lt.loot.tfs.io.TableOfContents;
import de.dfki.lt.loot.tfs.util.IntIDMap;
import de.dfki.lt.loot.tfs.util.ShortIDMap;

/** @author Bernd Kiefer
 *  This is a re-implementation of PET's grammar class
 *
 *  As far as i can see, this should now be fully thread safe. The only
 *  non-thread safe operation, unifyTypes, is now protected by a ReadWriteLock
 */
public class FSGrammar {

  private static final Logger LOGGER = Logger.getLogger(FSGrammar.class);

  private static final Logger infoLogger = Logger.getLogger("Info");

  /** This map maps from strings to (int) type ids and back */
  protected IntIDMap<String> _typeIdMap;

  /** This map maps from strings to (short) feature ids and back */
  protected ShortIDMap<String> _featureIdMap;

  /** This map maps from status names to (int) status ids and back.
   *  A type may be associated with a status, for example to mark rules,
   *  lexicon entries, etc.
   */
  protected IntIDMap<String> _statusIdMap;

  /** A type may be associated with a status, for example to mark rules,
   *  lexicon entries, etc.
   */
  protected TIntIntMap _type2Status;

  /** A very simple restrictor deleting all features mentioned here */
  protected TShortHashSet _featuresToDelete = null;

  /** Number of types in the grammar */
  protected int _grammarTypes;

  /** First leaf type == number of proper (non-leaf) types */
  protected int _firstLeafType;

  /** Number of all (grammar and dynamic) types */
  protected int _typeNo;

  /** Number of all known features */
  protected short _featureNo;

  /** store the skeleton feature structure for a type */
  protected TFS[] _typeFS;

  /** contains for every leaf type the single parent this type has.
   *  Remember that when accessing this array, one has to subtract the
   *  firstLeafType offset to get to the correct position.
   */
  protected int[] _leaftypeParent;

  /** The super/subtype structure of the proper types */
  protected TIntArrayList[] _parents, _children;

  /** cache computed type glbs in this map */
  protected TLongIntMap _glbCache;

  /** cache computed type glbs for subsumption in this map */
  protected TLongIntMap _glbCacheSubs;

  /** the bitcodes for all proper types, to compute glbs effectively */
  protected int[][] _bitcode;

  /** A mapping from bit codes to types */
  protected TObjectIntCustomHashMap<int[]> _bitcodeToType;

  /* ======================================================================
   * Information for a fixed arity encoding implementation of the dags
   * ====================================================================== */

  @SuppressWarnings("unused")
  private boolean _dagNocasts;
  private int[] _featSet;

  /** The number of feature set descriptors for this grammar */
  //private int _nFeatSets;
  /** The feature set descriptors for this grammar */
  short[][] _featSetDescriptors;

  /** contains the type where a feature was introduced for the first time */
  private int _appType[];

  /** contains the maximally appropriate type for a feature */
  private int _maxAppType[];

  /* ======================================================================
   * type and feature name constants
   * ====================================================================== */


  // TODO read this from a configuration
  /** in order to handle unknown string types, we need to know the name of the
   * string type (which is assumed to be the super type of these unknown types)
   */
  public static String STRING_TYPE_NAME = "string";
  public static String NULL_TYPE_NAME = "*null*";
  public static String CONS_TYPE_NAME = "*cons*";
  public static String DLIST_TYPE_NAME = "*diff-list*";

  public static String QC_TYPE_NAME = "$qc_paths_set";
  public static String TRUE_TYPE_NAME = "+";

  /*
  // CCG2AVM
  public static String FIRST_FEATURE_NAME = "CAR";
  public static String REST_FEATURE_NAME = "CDR";
  public static String ARGS_FEATURE_NAME = "DTRS";
  */
  // ERG /Delph-IN
  public static String FIRST_FEATURE_NAME = "FIRST";
  public static String REST_FEATURE_NAME = "REST";

  public static String LIST_FEATURE_NAME = "LIST";
  public static String LAST_FEATURE_NAME = "LAST";

  public static String ARGS_FEATURE_NAME = "ARGS";

  public static String ATOM_STATUS_NAME = "*atom*";
  public static String RULE_STATUS_NAME = "rule";

  /** Cached code for the atom status */
  protected final int atomStatusId;

  /* ======================================================================
   * type constants
   * ====================================================================== */

  public static final short ILLEGAL_FEATURE = -1;

  private static final int INT_SIZE = 32;

  /** The type code representing failure (the bottom of the hierarchy) */
  public static int BOTTOM_TYPE = -1;

  /** The type code representing the most general type
   *  (the top of the hierarchy)
   */
  public static int TOP_TYPE;

  /** stores the type identifier (an int) for the string, cons, null
   *  and diff-list type
   */
  public final int stringTypeId, consTypeId, nullTypeId, dListTypeId;

  /** The type representing "true" */
  public final int trueTypeId;

  /* ======================================================================
   * feature constants
   * ====================================================================== */

  /** The feature id for the CAR of a FS cons */
  public final short firstFeatureId;

  /** The feature id for the CDR of a FS cons */
  public final short restFeatureId;

  /** The feature id for the LIST of a difference list */
  public final short listFeatureId;

  /** The feature id for the LAST of a difference list */
  public final short lastFeatureId;

  /** The feature id for the ARGS of a rule FS */
  public final short argsFeatureId;


  /* ======================================================================
   * path constants
   * ====================================================================== */

  /** The path to the keyarg marker */
  public final List<Short> keyargMarkerPath;

  /* ======================================================================
   * bit code methods
   * ====================================================================== */

  /** Return the bit code representation for a type
   *  Bit codes are only stored for proper types, leaf types can be handled
   *  more efficiently and with less space requirements.
   */
  private int[] getBitcode(int type) {
    return this._bitcode[type];
  }

  /** return the type associated with the given bitcode */
  private int getType(int[] bitcode) {
    if (bitcode == null)
      return BOTTOM_TYPE;
    return _bitcodeToType.get(bitcode);
  }

  /** return true if code1 is subsumed by code 2, that is, if all set bits in
   *  code2 are also set in code1
   */
  private boolean subsumesCode(int[] code1, int[] code2) {
    // all bit codes have the same length
    for (int i = 0; i < code1.length; ++i) {
      if ((code1[i] & code2[i]) != code2[i])
        return false;
    }
    return true;
  }

  /** To unify to bit vectors, we have to compute their intersection.
   *  @return a new bit vector that is the intersection of the arguments, or
   *  null, if the result would contain no set bit.
   */
  private int[] unifyCodes(int[] code1, int[] code2) {
    int[] result = new int[code1.length];
    boolean set = false;
    for (int i = 0; i < code1.length; ++i) {
      result[i] = code1[i] & code2[i];
      set |= (result[i] != 0);
    }
    return set ? result : null;
  }

  /* ======================================================================
   * constructors
   * ====================================================================== */

  /** Read the contents of this grammar from a flop-generated binary file */
  public FSGrammar(String filename) {
    _type2Status = new TIntIntHashMap();
    _statusIdMap = new IntIDMap<String>();
    _typeIdMap = new IntIDMap<String>();
    _featureIdMap = new ShortIDMap<String>();

    loadGrammar(filename);

    atomStatusId = _statusIdMap.register(ATOM_STATUS_NAME);

    getNumberForTypeName("*TOP*");

    // finally assign the type number to the instance field stringType, used
    // during type unification and subsumption with unknown (string) types
    stringTypeId = getNumberForTypeName(STRING_TYPE_NAME);

    consTypeId = getNumberForTypeName(CONS_TYPE_NAME);
    nullTypeId = getNumberForTypeName(NULL_TYPE_NAME);

    dListTypeId = getNumberForTypeName(DLIST_TYPE_NAME);

    trueTypeId = getNumberForTypeName(TRUE_TYPE_NAME);

    firstFeatureId = getNumberForFeatureName(FIRST_FEATURE_NAME);
    restFeatureId = getNumberForFeatureName(REST_FEATURE_NAME);

    listFeatureId = getNumberForFeatureName(LIST_FEATURE_NAME);
    lastFeatureId = getNumberForFeatureName(LAST_FEATURE_NAME);

    argsFeatureId = getNumberForFeatureName(ARGS_FEATURE_NAME);

    keyargMarkerPath = new ArrayList<Short>(1);
    keyargMarkerPath.add(getNumberForFeatureName("KEY-ARG"));

    _glbCache = new TLongIntHashMap(30000, 0.5f, 0, -2);

    _glbCacheSubs = new TLongIntHashMap(30000, 0.5f, 0, -2);

    // _grammarTypes = 1; // only the TOP type is a proper type

    TFS.setGrammar(this);
  }

  /* ======================================================================
   * General feature handling functions
   * ====================================================================== */

  /** Return the number of features known to the grammar */
  public short getNoOfFeatures() {
    return _featureNo;
  }

  /** Return the feature id for the given feature name, or ILLEGAL_FEATURE, if
   *  the name is not known
   */
  public short getFeatureId(String featureName) {
    return (this._featureIdMap.contains(featureName)
        ? this._featureIdMap.getId(featureName) : ILLEGAL_FEATURE);
  }

  /** Return the feature name connected to the given feature id, or null, if
   *  feature >= getNoOfFeatures()
   */
  public String getFeatureName(short feature) {
    return this._featureIdMap.fromId(feature);
  }

  /** create a new feature id for the given name, or return an already known one
   */
  protected short getNumberForFeatureName(String name) {
    if (! this._featureIdMap.contains(name)) {
      return _featureIdMap.register(name);
    }
    return this._featureIdMap.getId(name);
  }


  /** The features added via this function form a simple restrictor for parsing
   */
  public void addFeatureToDelete(String feat) {
    short feature = getFeatureId(feat);
    if (feature != ILLEGAL_FEATURE) {
      if (_featuresToDelete == null) {
        _featuresToDelete = new TShortHashSet();
      }
      _featuresToDelete.add(feature);
    }
  }

  /** Clear the simple restrictor for parsing */
  public void clearFeaturesToDelete() {
    if (_featuresToDelete != null)
      _featuresToDelete.clear();
  }

  /** Return true if the given feature is not to be deleted */
  public boolean keepFeature(short feature) {
    if (_featuresToDelete == null) return true;
    return ! _featuresToDelete.contains(feature);
  }

  /** Return the type introducing a feature */
  public int getAppropriateType(short feature) {
    return _appType[feature];
  }

  /** Return the maximally appropriate type for a feature */
  public int getMaxAppropriateType(short feature) {
    return _maxAppType[feature];
  }

  /* ======================================================================
   * General type handling functions
   * ====================================================================== */

  /** Return the number of types coming from the grammar (not dynamically
   *  created)
   */
  public int getNoOfGrammarTypes() { return _grammarTypes; }

  /** Return the total number of types (including dynamically created ones) */
  public int getNoOfTypes() { return _typeNo; }

  /** Return true, if the given type id is one from the grammar */
  public boolean isGrammarType(int type) { return (type < _grammarTypes); }

  /** return true if the type is a "proper" type, that is, not a leaf type */
  public boolean isProperType(int type) { return (type < _firstLeafType); }

  /** return true if the type's subtypes form a tree */
  public boolean isLeafType(int type) {
    return (type >= _firstLeafType) && (type < _typeNo);
  }

  /** Return the type id for the given type name, or BOTTOM_TYPE, if
   *  the name is not known
   */
  public int getTypeId(String typeName) {
    return (this._typeIdMap.contains(typeName)
        ? this._typeIdMap.getId(typeName) : BOTTOM_TYPE);
  }

  /** Return the type name for the given type id, or null, if the id is not
   *  known
   */
  public String getTypeName(int type) { return this._typeIdMap.fromId(type); }

  /** create a new type id for the given name, or return a known one */
  public int getNumberForTypeName(String typeName) {
    // obtain the type id for the type name
    if (! _typeIdMap.contains(typeName)) {
      int result = _typeIdMap.register(typeName);
      // if so, make it an atomic type
      _type2Status.put(result, atomStatusId);
      return result;
    }
    return _typeIdMap.getId(typeName);
  }

  /** return the leaf type parent of the given type, or BOTTOM_TYPE, if type
   *  is not a leaf type.
   */
  public int getLeafTypeParent(int type) {
    assert(isLeafType(type));

    if (! isGrammarType(type)) return TOP_TYPE;
    // note that the parameter type >= this.firstLeafType, hence we must map
    // type to the right index in the delta array, since leafTypeparent starts
    // with index 0:
    return _leaftypeParent[type - this._firstLeafType];
  }

  /** return the supertype(s) of some type */
  public int[] superTypes(int type) {
    int[] result = null;
    if (isLeafType(type)) {
      result = new int[1];
      result[0] = getLeafTypeParent(type);
    } else {
      TIntArrayList supers = _parents[type];
      result = new int[supers.size()];
      for (int i = 0; i < supers.size(); ++i) {
        result[i] = supers.get(i);
      }
    }
    return result;
  }

  /** return the subtype(s) of some type (currently only for proper types */
  public int[] subTypes(int type) {
    int[] result = null;
    if (isLeafType(type)) {
      //result = new int[1];
      //result[0] = getLeafTypeParent(type);
    } else {
      TIntArrayList subs = _children[type];
      result = new int[subs.size()];
      for (int i = 0; i < subs.size(); ++i) {
        result[i] = subs.get(i);
      }
    }
    return result;
  }

  /* ======================================================================
   * type subsumption / unification functions
   * ====================================================================== */

  /** Is type1 more general than type2, i.e. is type2 a subtype of type1? */
  public boolean subsumesType(int type1, int type2) {
    return (unifyTypesSubs(type1, type2) == type2);
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
    return subsumesCode(getBitcode(t2), getBitcode(t1));
  }

  protected boolean subTypeBothLeafTypes(int t1, int t2) {
    if (t1 == t2) return true;
    if (isLeafType(t1))
      return subTypeBothLeafTypes(getLeafTypeParent(t1), t2);
    return false;
  }

  boolean[] lockSubs = { false };

  /** Fully thread safe by synchronizing the glb cache with an efficient lock */
  public int unifyTypesSubs(int t1, int t2) {
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

    if (! isGrammarType(t2)) return BOTTOM_TYPE;
    // typeIdent2 may not be TOP_TYPE) since TOP has the
    // smallest ident and tI1 <= tI2

    // now obtain the (unique long) integer code for the GLB of tI1 and tI2
    // TODO this is wrong given that types could be added !
    long idx = t2 + _typeNo * t1;
    while (lockSubs[0]) {
      synchronized(lockSubs) {

      }
    }
    int val = _glbCacheSubs.get(idx);
    if (val != -2)
      return val;

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
        result = getType(
            unifyCodes(getBitcode(t2), getBitcode(t1)));
      }
    }

    synchronized(lockSubs) {
      lockSubs[0] = true;
      this._glbCacheSubs.put(idx, result);
      lockSubs[0] = false;
      lockSubs.notifyAll();
    }

    return result;
  }

  boolean[] lock = { false };

  /** Fully thread safe by synchronizing the glb cache with an efficient lock */
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
    // TODO this is wrong given that types could be added !
    long idx = t2 + _typeNo * t1;
    while (lock[0]) {
      synchronized(lock) {

      }
    }
    int val = _glbCache.get(idx);
    if (val != -2)
      return val;

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
        result = getType(
            unifyCodes(getBitcode(t2), getBitcode(t1)));
      }
    }

    synchronized(lock) {
      lock[0] = true;
      this._glbCache.put(idx, result);
      lock[0] = false;
      lock.notifyAll();
    }

    return result;
  }

  /** Save a filled GLB cache to file, as a triple of type1, type2, result.
   *  type2 is always smaller than type1, and to reconstruct the cache,
   *  the pair (type1 + _typeNo * type2, result) must be put into the map.
   */
  public void dumpGlbCache(final Writer out) {
    synchronized(_glbCache) {
      _glbCache.forEachEntry(new TLongIntProcedure() {
        private final String nl = System.getProperty("line.separator");
        @Override
        public boolean execute(long argTypes, int resType) {
          try {
            int type1 = (int) (argTypes % _typeNo);
            int type2 = (int) (argTypes / _typeNo);
            assert(type1 + _typeNo * type2 == argTypes);
            out.append(Integer.toString(type1)).append(' ');
            out.append(Integer.toString(type2)).append(' ');
            out.append(Integer.toString(resType)).append(nl);
          } catch (IOException ex) {
            LOGGER.error("Error during dump of glb cache: " + ex);
            return false;
          }
          return true;
        }
      });
    }
  }


  /** Load a saved GLB cache from a file with triples of type1, type2, result.
   *  type2 is always smaller than type1, and to reconstruct the cache,
   *  the pair (type1 + _typeNo * type2, result) must be put into the map.
   */
  public TLongIntMap undumpGlbCache(Reader inReader) {
    final TLongIntMap cache = new TLongIntHashMap();
    final BufferedReader in = new BufferedReader(inReader);
    String line;
    synchronized(cache) {
      cache.clear();
      try {
        while ((line = in.readLine()) != null) {
          String[] entryStrings = line.split("\\s+");
          assert(entryStrings.length == 3);
          int type1 = Integer.parseInt(entryStrings[0]);
          int type2 = Integer.parseInt(entryStrings[1]);
          int resType = Integer.parseInt(entryStrings[2]);
          cache.put(type1 + _typeNo * type2, resType);
        }
      }
      catch (IOException ex) {
        LOGGER.error("Error while loading glb cache: " + ex);
      }
      catch (NumberFormatException ex) {
        LOGGER.error("Error while loading glb cache: " + ex);
      }
    }
    return cache;
  }


  /** Return a map of second unification arg --> result type for a given
   *  input type.
   */
  public TIntIntMap getUnificationTypes(TLongIntMap cache, final int type) {
    final TIntIntMap result = new TIntIntHashMap();
    cache.forEachEntry(new TLongIntProcedure() {
      @Override
      public boolean execute(long argTypes, int resType) {
        int type1 = (int) (argTypes % _typeNo);
        int type2 = (int) (argTypes / _typeNo);
        if (type1 == type)
          result.put(type2, resType);
        else if (type2 == type)
          result.put(type1, resType);
        return true;
      }
    });
    return result;
  }

  private TIntIntMap _dist = new TIntIntHashMap();

  public int getTopDistance(int type) {
    if (_dist.containsKey(type))
      return _dist.get(type);
    int dist = Integer.MAX_VALUE;
    if (type == TOP_TYPE) {
      dist = 0;
    } else {
      for (int superType : superTypes(type)) {
        dist = Math.min(dist, getTopDistance(superType));
      }
    }
    ++dist;
    _dist.put(type, dist);
    return dist;
  }

  /* ======================================================================
   * Special Purpose features and types
   * ====================================================================== */

  /** Return the feature where to find the arguments of a rule fs */
  public short getArgsFeature() { return argsFeatureId; }

  /** Return the feature representing the CAR of an FS cons */
  public short getFirstFeature() { return firstFeatureId; }

  /** Return the feature representing the CDR of an FS cons */
  public short getRestFeature() { return restFeatureId; }

  /** Return the type id representing an FS cons */
  public int getConsType() { return consTypeId; }

  /** Return the type id representing an empty list */
  public int getNullType() { return nullTypeId; }


  /* ======================================================================
   * Type status handling (to distinguish rules, lex entries, etc.)
   * ====================================================================== */

  /** Return the status id for the given string */
  public int getStatusID(String name) {
    return this._statusIdMap.getId(name);
  }

  /** Return the status id for the given string */
  public String getStatusName(int statusId) {
    return this._statusIdMap.fromId(statusId);
  }

  /** Return the status id for the given type */
  public int getStatusForType(int type) {
    return this._type2Status.get(type);
  }

  /** return all types associated with the rule status */
  public Iterable<Integer> getRuleTypes() {
    List<Integer> result = new ArrayList<Integer>();
    int ruleStatus = getStatusID(RULE_STATUS_NAME);
    for(int type = 0; type < getNoOfGrammarTypes(); ++type) {
      if (getStatusForType(type) == ruleStatus) {
        result.add(type);
      }
    }
    return result;
  }

  /* ======================================================================
   * FS handling
   * ====================================================================== */

  /** get the expanded (type) FS for the given type */
  public TFS getFS(int type) {
    return (isGrammarType(type) ? _typeFS[type] : new TFS(type));
  }

  /** get the expanded (type) FS for the given type */
  public TFS getFS(String typeName) {
    int id = getTypeId(typeName);
    if (id < 0) return null;
    return getFS(id);
  }

  /** return the dag associated with the quick check data structure */
  public TFS getQCDag() {
    int qcType = getTypeId(QC_TYPE_NAME);
    return (qcType != BOTTOM_TYPE ? getFS(qcType) : null);
  }

  /* ======================================================================
   * Grammmar loading
   * ====================================================================== */

  /** read the tables for type names, type -> status mappings and feature
   *  names.
   *  Format:
   *  #status (int)
   *  first leaftype == # proper types (int)
   *  #leaftypes (int)
   *  #attributes (int)
   *  list of status names (#status * (string))
   *  list of pairs (string, int) for typename, typestatus (#types times)
   *  list of attribute names (string) (#attributes times)
   *  @param u the undumper to read from
   */
  private void undumpSymbols(PetUndumper u) {

    infoLogger.info("reading symbol tables ...");

    int statusNo = u.undumpInt();
    LOGGER.debug("  # status: " + statusNo);

    _firstLeafType = u.undumpInt();
    infoLogger.info("  # proper types: " + _firstLeafType);

    int leafTypes = u.undumpInt();
    infoLogger.info("  # leaf types: " + leafTypes);

    _featureNo = (short) u.undumpInt();
    infoLogger.info("  # attributes: " + _featureNo);

    _typeNo = _grammarTypes = _firstLeafType + leafTypes;

    // create the missing tables
    this._statusIdMap = new IntIDMap<String>(statusNo);
    this._type2Status = new TIntIntHashMap(_typeNo);

    // establish a mapping from ints onto status names
    for (int i = 0; i < statusNo; ++i)
      _statusIdMap.register(u.undumpString());

    // read in the type tables and type -> status mappings
    _typeIdMap = new IntIDMap<String>(this._typeNo);
    for (int i = 0; i < _typeNo; i++) {
      String typeName = u.undumpString();
      int newId = _typeIdMap.register(typeName);
      assert(newId == i);
      int statId = u.undumpInt();
      _type2Status.put(i, statId); // status (int) of type (int)
    }

    // establish the feature mapping
    _featureIdMap = new ShortIDMap<String>(_featureNo);
    for (short i = (short) 0; i < _featureNo; ++i) {
      String featureName = u.undumpString();
      int newId = _featureIdMap.register(featureName);
      assert(newId == i);
    }
  }

  /** Read the bit codes and the table of leaf types from the undumper
   *  Format:
   *  bitcode_length (int)
   *  bitcode_length times (short) times #proper_types (== first_leaftype)
   *  #leaftypes times leaftypeparent (int)
   *  @param u the undumper to read from
   */
  private void undumpHierarchy(PetUndumper u) throws IOException {
    infoLogger.info("reading type hierarchy ...");

    int noOfBits = u.undumpInt();
    LOGGER.debug("  code length (# bits): " + noOfBits);
    // compute the number of ints for encoding the proper types
    int codesize = (noOfBits / FSGrammar.INT_SIZE) + 1;

    // create an array for all proper types containing the bit vectors of length
    // codesize
    _bitcode = new int[_firstLeafType][codesize];

    // and the mapping from bit vectors to types
    this._bitcodeToType = new TObjectIntCustomHashMap<int[]>(
        new HashingStrategy<int[]>() {
          private static final long serialVersionUID = 1L;

          public int computeHashCode(int[] arg) {
            int i = 0;
            while (i < arg.length && arg[i] == 0) { ++i; }
            return (i * INT_SIZE)
                + Integer.numberOfTrailingZeros(arg[i]);
          }

          public boolean equals(int[] arg0, int[] arg1) {
            return Arrays.equals(arg0, arg1);
          }
        }, _firstLeafType);

    // read in the code vector for the proper types
    for (int i = 0; i < _firstLeafType; ++i) {
      int[] code = u.undumpBitcode(codesize);
      _bitcodeToType.put(code, i);
      _bitcode[i] = code;
    }

    // For every leaf type, store its unique parent
    int leafTypes = _grammarTypes - _firstLeafType;
    _leaftypeParent = new int[leafTypes];
    for (int i = 0; i < leafTypes; ++i)
      _leaftypeParent[i] =  u.undumpInt();

    // done in the constructor
    // create the cache for glbs that have already been computed
    // this._glbCache = new TLongIntHashMap();
  }

  /** Store the immediate super- and subtypes for all proper types.
   *  @param u the undumper to read from
   *
   *  TODO extend to leaf types for _children, if that's needed, because only
   *  the parent structure is currently explicitely represented for them
   */
  private void undumpSuperTypes(PetUndumper u) {
    infoLogger.info("reading supertype structure ...");

    _parents = new TIntArrayList[_firstLeafType];
    _children = new TIntArrayList[_firstLeafType];

    for(int i = 0; i < _firstLeafType; ++i) {
      short noSuperTypes = u.undumpShort();
      this._parents[i] = new TIntArrayList(noSuperTypes);
      for (short s = 0; s < noSuperTypes; ++s) {
        int parent = u.undumpInt();
        this._parents[i].add(parent);
        if (this._children[parent] == null)
          this._children[parent] = new TIntArrayList(5);
        this._children[parent].add(i);
      }
    }
  }

  /** Tables for fixed arity encoding representation of feature structures.
   *  @param u the undumper to read from
   */
  private void undumpFeatureTables(PetUndumper u) {
    infoLogger.info("reading feature tables ...");

    int coding = u.undumpInt();

    switch (coding) {
    case 0: _dagNocasts = true; break;
    case 1: _dagNocasts = false; break;
    default:
      throw new IllegalArgumentException("unknown coding: " + coding);
    }

    _featSet = new int[_firstLeafType];
    for (int i = 0; i < _firstLeafType; ++i) {
      _featSet[i] = u.undumpInt();
    }

    int nFeatSets = u.undumpInt();
    _featSetDescriptors = new short[nFeatSets][];

    for(int i = 0; i < nFeatSets; ++i) {
      short na = u.undumpShort();
      short[] featSet = na > 0 ? new short[na] : null;

      for(int j = 0; j < na; ++j)
        featSet[j] = u.undumpShort();

      _featSetDescriptors[i] = featSet;
    }

    // read appropriate sorts table
    _appType = new int[_featureNo];
    for(int i = 0; i < _featureNo; ++i)
      _appType[i] = u.undumpInt();
  }

  // TODO fill in some time
  /** Currently not needed
   * @param u the undumper to read from
   *
  private void undumpFullforms(PetUndumper u) {
  }

  /** Currently not needed
   * @param u the undumper to read from
   *
  private void undumpInflectionRules(PetUndumper u) {
  }

  /** Currently not needed
   * @param u the undumper to read from
   *
  private void undumpIrregulars(PetUndumper u) {
  }
  */

  /** Read the (expanded, maybe unfilled) feature structures from the stream.
   * @param u the undumper to read from
   */
  private void undumpDags(PetUndumper u) {
    infoLogger.info("reading constraints ...");

    _typeFS = new TFS[this._typeNo];
    // successively read in the dumped FSs
    for (int i = 0; i < this._typeNo; ++i) {
      _typeFS[i] = TFS.buildFS(u);
    }
    LOGGER.debug("  # created nodes: " + DagNode.totalNoNodes);
    LOGGER.debug("  # created arcs: " + DagNode.totalNoArcs);
  }


  /** Initialise the array of maximally appropriate types under a feature */
  private void initializeMaxapp() {
    _maxAppType = new int[_featureNo];
    for(short i = 0; i < _featureNo; ++i) {
      _maxAppType[i] = 0;
      // the direct access to typedag[] is ok here because no dynamic type
      // can be appropriate for a feature
      DagNode cval = _typeFS[_appType[i]].dag().getValue(i);
      if(cval != null)
        _maxAppType[i] = cval.getType();
    }
  }

  /**
   * loadGrammar() contains the grammar loading calls from the PET
   * tGrammar constructor.
   */
  public void loadGrammar(String filename) {
    long time = System.currentTimeMillis();
    PetUndumper u = null;
    // read in the binary file
    try {
      // now read the complete grm file into the byte array
      u = new PetUndumper();
      u.open(new File(filename));

      infoLogger.info("reading table of contents ...");
      TableOfContents toc = new TableOfContents(u);

      // read symbol tables for int-to-type/feature mappings;
      toc.gotoSection(TableOfContents.Section.SYMTAB);
      undumpSymbols(u);

      // read in the print names of types,
      //toc.gotoSection(TableOfContents.Section.PRINTNAMES);
      //undumpPrintNames(u);

      // read in the hierarchy,
      toc.gotoSection(TableOfContents.Section.HIERARCHY);
      undumpHierarchy(u);

      // tables for fixed arity encoding of feature structures
      toc.gotoSection(TableOfContents.Section.FEATTABS);
      undumpFeatureTables(u);

      // read in the full form "morphology"
      //toc.gotoSection(TableOfContents.Section.FULLFORMS);
      //undumpFullforms(u);

      // read in the inflection rules morphology
      //toc.gotoSection(TableOfContents.Section.INFLR);
      //undumpInflectionRules(u);

      // read the irregular morphological forms
      //toc.gotoSection(TableOfContents.Section.IRREGS);
      //undumpIrregulars(u);

      // read in the constraints for proper and leaf types
      toc.gotoSection(TableOfContents.Section.CONSTRAINTS);
      undumpDags(u);
      initializeMaxapp(); // needs feature tables AND dags

      // read the properties for the statistical models
      //toc.gotoSection(TableOfContents.Section.PROPERTIES);
      //undumpProperties(u);

      // read in the hierarchy of proper types
      toc.gotoSection(TableOfContents.Section.SUPERTYPES);
      undumpSuperTypes(u);

    } catch (IOException ioe) {
      LOGGER.error("Error while reading grammar from " + filename + ": " + ioe);
      System.exit(1);
    } finally {
      try {
        // and finally close the stream and free the memory
        if (u != null) u.close();
      }
      catch (IOException ioex) {
        LOGGER.error("Error while closing grammar file " + filename + ": " + ioex);
      }
    }
    infoLogger.info("overall load time: "
        + ((System.currentTimeMillis() - time) / 1000.0) + " secs");
  }


  /* ======================================================================
   * Miscellaneous methods
   * ====================================================================== */

  /** Read TFSs from the given input stream.
   *
   * @param in a Reader to read from
   * @param consumer a Consumer that processes the TFSs
   * @throws InvalidSyntaxException
   */
 public static void readTFSReader(Reader in, Consumer consumer)
     throws InvalidSyntaxException {
   try {
     JxchgTokenizer tok = new JxchgTokenizer(in);
     tok.readEdges(consumer);
   } catch (IOException ioex) {
     LOGGER.warn(ioex);
   }
 }

  /** read the specified (possibly compressed) jxchg files.
   *
   *  The second possibility is reading a file consisting of TFSs only in JXCHG
   *  format and returning them as a list; this is done if consumer is
   *  <code>null</code>
   *
   *  @param file the file to read from (may be gzip compressed, then, it has to
   *              have a .gz file suffix)
   *  @param consumer if <code>null</code>, read a file of TFSs into a list, if
   *         not, read a chart format JXCHG file, and the return value is
   *         <code>null</code>
   *
   */
  public static void readTFSFile(File file, Consumer consumer) {
    try {
      readTFSReader(JxchgTokenizer.getReader(file), consumer);
    } catch (FileNotFoundException fnfex) {
      LOGGER.warn(fnfex);
    } catch (IOException ioex) {
      LOGGER.warn(ioex);
    } catch (InvalidSyntaxException isex) {
      File moveTo =
        new File(file.getParent() + File.separator + "bad" + File.separator
            + file.getName());
      boolean moved = file.renameTo(moveTo);
      LOGGER.warn(isex.getMessage() + " in " + file
          + " was " + (moved ? "" : "not ") +  "moved to `bad' ");
    }
  }

  /** @see readTFSFile(File file, EdgeConsumer consumer, int maxFS)
   */
  public static void readTFSFile(String fileName, Consumer consumer) {
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

  public List<Integer> getTypesWithStatusId(final int statusId) {
    final List<Integer> result = new ArrayList<Integer>();
    _type2Status.forEachEntry(new TIntIntProcedure() {
      @Override
      public boolean execute(int a, int b) {
        if (b == statusId) result.add(a);
        return true;
      }
    });
    return result;
  }
}
