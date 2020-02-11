package de.dfki.lt.loot.tfs;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import gnu.trove.map.TLongIntMap;
import gnu.trove.map.hash.TLongIntHashMap;
import gnu.trove.set.hash.TShortHashSet;

import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Properties;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.junit.Before;
import org.junit.Test;

import de.dfki.lt.loot.tfs.io.InvalidSyntaxException;

public class UnifTest {

  private static final boolean DISPLAY = true;

  private static Logger logger;


  // WATCH OUT: the Tomabechi unifier can not properly deal with cyclic
  // structures, as can be seen in the example unif(9, 12), where it fails in
  // one direction to get the REST feature, depending on how the forward pointer
  // is set.
  protected static String base[] = {
    "[ *cons* FIRST [ *top* ] ]",   // 0
    "[ *cons* FIRST [ *top* ] REST [ *top* ] ]", // 1
    "[ *cons* FIRST [ *top* ] REST [ *cons* FIRST [ f ] ] ]", // 2
    "[ *cons* FIRST [ *cons* ] ]" , // 3
    "[ *cons* FIRST # 1 [ f ] REST [ *cons* FIRST # 1 ] ]", // 4
    "[ *cons* FIRST # 1 [ f ] ARGS [ *top* ] REST [ *cons* FIRST # 1 ] ]", //5
    "[ *cons* FIRST # 1 [ j ] ARGS [ *top* FIRST [ j ] ]" +
    "         REST [ *cons* FIRST # 1 ] ]", //6
    "[ *cons* FIRST # 1 [ j ] REST # 2 [ *cons* FIRST # 1 ] ARGS # 2 ]", // 7
    "[ *cons* FIRST [ *cons* FIRST # 1 [ *top* ARGS [ *top* ] ]" +
    "                        REST # 1 ] ]", // 8
    "[ *cons* FIRST [ *cons* FIRST # 1 [ *top* FIRST [ *top* ] ARGS # 2 [ *top* ] ]" +
    "                        REST # 1 ]" +
    "         ARGS # 2 ]",  // 9
    "[ *cons* FIRST #1 [ j ] REST #1 ]", // 10
    "[ *cons* FIRST [ j ] REST [ j ] ]", // 11
    "[ *cons* FIRST #1 [ *cons* FIRST #1 ] ]", // 12
  };

  protected static String createExtra[] = {
    // check cycle
    "[ *cons* FIRST #1 [ *top* ARGS #1 ] REST #2 [ *cons* FIRST #1 REST #2 ] ]",
    "[ *top* ARGS [ *top* FIRST # 1 [ *top* ARGS [ *top* ] REST # 1 ] ]" +
        " REST [ *top* FIRST [ *top ] REST [ *top* ] ] ]",
    "[ h FIRST # 1 [ f ARGS [ *top* ] REST # 1 ] REST [ h FIRST [ h ] REST [ g ] ] ]",
    "# 1 [ *top* FIRST # 1 ]"
  };

  protected static String partTest[] = {
    "[ *cons* FIRST #1 [ *top* ] REST [ *list* FIRST #1 ] ]",
    "[ *cons* FIRST [ g  G [ *top* ] ] REST [ *list* FIRST [ h ] ] ]",
    "[ *cons* FIRST #1 [ i G [ *top* ] H [ *top* ] I [ *top* ] ] REST [ *list* FIRST #1 ] ]",
  };

  protected static String description[] = {
    "wellformedness unification"
  };

  protected static TFS tfs[] ;
  protected static TFS afs[] ;
  protected static TFS bfs[] ;

  protected static int corefNo[] = { 0, 0, 0, 0, 1, 1, 1, 2, 1, 2, 1, 0, 1 };
  protected static int corefNoRigid[] = { 0, 0, 0, 0, 1, 1, 1, 2, 2, 3, 1, 0, 1 };

  protected static int subsResults[] = {
      // 0 vs.
      DagNode.THIS_MORE_GENERAL + DagNode.ARG_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      // 1 vs
      DagNode.ARG_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL + DagNode.ARG_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      0,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      0,
      0,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      0,
      // 2 vs
      DagNode.ARG_MORE_GENERAL,
      DagNode.ARG_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL + DagNode.ARG_MORE_GENERAL,
      0,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      // 3 vs
      DagNode.ARG_MORE_GENERAL,
      0,
      0,
      DagNode.THIS_MORE_GENERAL + DagNode.ARG_MORE_GENERAL,
      0,
      0,
      0,
      0,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      0,
      0,
      DagNode.THIS_MORE_GENERAL,
      // 4 vs
      DagNode.ARG_MORE_GENERAL,
      DagNode.ARG_MORE_GENERAL,
      DagNode.ARG_MORE_GENERAL,
      0,
      DagNode.THIS_MORE_GENERAL + DagNode.ARG_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      // 5 vs
      DagNode.ARG_MORE_GENERAL,
      DagNode.ARG_MORE_GENERAL,
      DagNode.ARG_MORE_GENERAL,
      0,
      DagNode.ARG_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL + DagNode.ARG_MORE_GENERAL,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      // 6 vs
      DagNode.ARG_MORE_GENERAL,
      DagNode.ARG_MORE_GENERAL,
      0,
      0,
      0,
      0,
      DagNode.THIS_MORE_GENERAL + DagNode.ARG_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      0,
      0,
      0,
      0,
      0,
      // 7 vs
      DagNode.ARG_MORE_GENERAL,
      DagNode.ARG_MORE_GENERAL,
      0,
      0,
      0,
      0,
      DagNode.ARG_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL + DagNode.ARG_MORE_GENERAL,
      0,
      0,
      0,
      0,
      0,
      // 8 vs
      DagNode.ARG_MORE_GENERAL,
      0,
      0,
      DagNode.ARG_MORE_GENERAL,
      0,
      0,
      0,
      0,
      DagNode.THIS_MORE_GENERAL + DagNode.ARG_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL,
      0,
      0,
      0,
      // 9 vs
      DagNode.ARG_MORE_GENERAL,
      0,
      0,
      DagNode.ARG_MORE_GENERAL,
      0,
      0,
      0,
      0,
      DagNode.ARG_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL + DagNode.ARG_MORE_GENERAL,
      0,
      0,
      0,
      // 10 vs
      DagNode.ARG_MORE_GENERAL,
      DagNode.ARG_MORE_GENERAL,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      DagNode.THIS_MORE_GENERAL + DagNode.ARG_MORE_GENERAL,
      DagNode.ARG_MORE_GENERAL,
      0,
      // 11 vs
      DagNode.ARG_MORE_GENERAL,
      DagNode.ARG_MORE_GENERAL,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      DagNode.THIS_MORE_GENERAL,
      DagNode.THIS_MORE_GENERAL + DagNode.ARG_MORE_GENERAL,
      0,
      // 11 vs
      DagNode.ARG_MORE_GENERAL,
      0,
      0,
      DagNode.ARG_MORE_GENERAL,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      0,
      DagNode.THIS_MORE_GENERAL + DagNode.ARG_MORE_GENERAL,
  };

  protected static boolean unifResults[] = {
    true, true, true, true, true, true, true, true, true, true, true, true, false,
    true, true, true, true, true, true, true, true, true, true, true, true, false,
    true, true, true, true, true, true, false, false, true, true, false, false, false,
    true, true, true, true, false, false, false, false, true, true, false, false, false,
    true, true, true, false, true, true, false, false, false, false, false, false, false,
    true, true, true, false, true, true, false, false, false, false, false, false, false,
    true, true, false, false, false, false, true, true, false, false, false, false, false,
    true, true, false, false, false, false, true, true, false, false, false, false, false,
    true, true, true, true, false, false, false, false, true, true, false, false, false,
    true, true, true, true, false, false, false, false, true, true, false, false, false,
    true, true, false, false, false, false, false, false, false, false, true, true, false,
    true, true, false, false, false, false, false, false, false, false, true, true, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
  };

  protected static FSGrammar gram = null;

  public static File getTestResourceDir() {
    String relativePath = "src/test/resources/";
    Properties sysProps = System.getProperties();
    String basedir = (String) sysProps.get("basedir");
    if (basedir != null) {
      return new File(basedir, relativePath);
    }
    return new File(relativePath);
  }

  @Before public void setUp() {
    File resourceDir = getTestResourceDir();

    if (gram == null)
      gram = new FSGrammar(
          new File(resourceDir, "minimal/uniftest.grm")
          .getAbsolutePath());
    tfs = new TFS[partTest.length];
    for (int ii = 0; ii < partTest.length; ++ii) {
      try {
        tfs[ii] = TFS.fsFromString(partTest[ii]);
      } catch (Exception ex) {
        ex.printStackTrace(); System.exit(1);
      }
    }
    afs = new TFS[base.length];
    bfs = new TFS[base.length];
    for (int ii = 0; ii < base.length; ++ii) {
      try {
        afs[ii] = TFS.fsFromString(base[ii]);
        bfs[ii] = TFS.fsFromString(base[ii]);
      } catch (Exception ex) {
        ex.printStackTrace(); System.exit(1);
      }
    }
    // if (DISPLAY) { de.dfki.lt.loot.tfsviz.DagModelAdapter.init(); }
  }

  public void testCreationOne(int i) {
    logger = LoggerFactory.getLogger("testCreation");
    assertTrue("AFS not created:" + i , afs[i] != null);
    assertTrue("BFS not created:" + i , bfs[i] != null);
    //if (i == 9 && DISPLAY) TFSDisplay.displayAndWait(afs[i], bfs[i]);
  }

  @Test public void testCreation() throws InvalidSyntaxException {
    for (int i = 0; i < base.length; ++i) {
      testCreationOne(i);
    }
    for (int i = 0; i < createExtra.length; ++i) {
      assertNotNull("Extra FS not created: " + i, TFS.fsFromString(createExtra[i]));
    }
  }

  public void testCreationPartOne(int i) {
    logger = LoggerFactory.getLogger("testCreation");
    assertTrue("TFS not created: "+ i, tfs[i] != null);
  }

  @Test public void testCreationPart() {
    for (int i = 0; i < partTest.length; ++i) {
      testCreationPartOne(i);
    }
  }

  @Test public void testTypeUnification() {
    assertEquals(gram.getTypeId("$k"),
        gram.unifyTypes(gram.getTypeId("$k"),gram.getTypeId("rule")));
    assertEquals(gram.getTypeId("i"),
        gram.unifyTypes(gram.getTypeId("f"),gram.getTypeId("i")));
    assertEquals(gram.getTypeId("h"),
        gram.unifyTypes(gram.getTypeId("f"),gram.getTypeId("h")));
    assertEquals(gram.getTypeId("g"),
        gram.unifyTypes(gram.getTypeId("f"),gram.getTypeId("g")));
    assertEquals(FSGrammar.BOTTOM_TYPE,
        gram.unifyTypes(gram.getTypeId("f"),gram.getTypeId("*list*")));
  }

  public void testCorefCountOne(int i) {
    logger = LoggerFactory.getLogger("testBiSubsumption");
    int result = afs[i].countCorefs();
    afs[i].invalidate();
    if (result != corefNo[i])
      logger.info("Testing Corefs " + i + " "+ result + " " + corefNo[i]);
    assertEquals("" + i, corefNo[i], result);
  }

  @Test public void testCorefCount() {
    for (int i = 7; i < base.length; ++i) {
      testCorefCountOne(i);
    }
  }

  public void testCorefCountRigidOne(int i) {
    logger = LoggerFactory.getLogger("testBiSubsumption");
    int result = afs[i].countCorefsRigid();
    afs[i].invalidate();
    if (result != corefNoRigid[i])
      logger.info("Testing Corefs " + i + " "+ result + " " + corefNo[i]);
    assertEquals("At FS " + i, corefNoRigid[i], result);
  }

  @Test public void testCorefCountRigid() {
    for (int i = 7; i < base.length; ++i) {
      testCorefCountRigidOne(i);
    }
  }

  public void testBiSubsumptionOne (int i, int j) {
    logger = LoggerFactory.getLogger("testBiSubsumption");
    int result = afs[i].subsumesBi(bfs[j]);
    String s = "WHAT?";
    switch (result) {
    case DagNode.THIS_MORE_GENERAL : s = "this"; break;
    case DagNode.ARG_MORE_GENERAL : s = "arg"; break;
    case DagNode.THIS_MORE_GENERAL | DagNode.ARG_MORE_GENERAL: s = "equal"; break;
    case 0: s = "none"; break;
    }
    if (subsResults[j + base.length * i] != result) {
      logger.info("Testing " + i + " vs. "+ j + " " + s);
      //if (DISPLAY) TFSDisplay.displayAndWait(afs[i], bfs[j]);
    }
    assertEquals("" + i + ":" + j, subsResults[j + base.length * i], result);
  }

  @Test public void testBiSubsumption() {
    for (int i = 0; i < base.length; ++i) {
      for (int j = 0; j < base.length; ++j) {
        //if (j == 0 && i == 1)
        testBiSubsumptionOne(i, j);
      }
    }
  }

  public void testBiSubsumptionVsEqualsOne (int i, int j) {
    logger = LoggerFactory.getLogger("testBiSubsumptionVsEquals");
    boolean eqfwresult = afs[i].equals(bfs[j]);
    boolean eqbwresult = bfs[j].equals(afs[i]);
    if (eqfwresult != eqbwresult) {
      logger.info("Equals not symmetric:" + i + " vs. " + j
          + " fw: " + eqfwresult + " bw: " + eqbwresult);
      //if (DISPLAY) TFSDisplay.displayAndWait(afs[i], bfs[j]);
    }

    int result = afs[i].subsumesBi(bfs[j]);
    String s = "WHAT?";
    switch (result) {
    case DagNode.THIS_MORE_GENERAL : s = "this"; break;
    case DagNode.ARG_MORE_GENERAL : s = "arg"; break;
    case DagNode.THIS_MORE_GENERAL | DagNode.ARG_MORE_GENERAL: s = "equal"; break;
    case 0: s = "none"; break;
    }
    boolean subsresult =
      result == (DagNode.THIS_MORE_GENERAL | DagNode.ARG_MORE_GENERAL);
    if (eqfwresult != subsresult) {
      logger.info("Equals != SubsBi " + i + " vs. "+ j + " " +
          " eq: " + eqfwresult + " subsBi: " + s);
      //if (DISPLAY) TFSDisplay.displayAndWait(afs[i], bfs[j]);
    }
    assertEquals(eqfwresult, eqbwresult);
    assertEquals(subsresult, eqfwresult);
  }

  @Test public void testBiSubsumptionVsEquals() {
    for (int i = 0; i < base.length; ++i) {
      for (int j = 0; j < base.length; ++j) {
        //if (i == 4 && j == 4)
        testBiSubsumptionVsEqualsOne(i, j);
      }
    }
  }

  public void testSubsumptionOne(int i, int j) {
    logger = LoggerFactory.getLogger("testSubsumption");
    int result = afs[i].subsumesBi(bfs[j]);
    if ((result & DagNode.THIS_MORE_GENERAL) != 0)
      assertTrue("" + i + ":" + j, afs[i].subsumes(bfs[j]));
    if ((result & DagNode.ARG_MORE_GENERAL) != 0)
      assertTrue("" + i + ":" + j, bfs[j].subsumes(afs[i]));
    if ((result & DagNode.ARG_MORE_GENERAL) != 0)
      assertTrue("" + i + ":" + j, afs[i].dag().isSubsumedBy(bfs[j].dag()));
    if ((result & DagNode.THIS_MORE_GENERAL) != 0)
      assertTrue("" + i + ":" + j, bfs[j].dag().isSubsumedBy(afs[i].dag()));  }

  @Test public void testSubsumption() {
    for (int i = 0; i < base.length; ++i) {
      for (int j = 0; j < base.length; ++j) {
        testSubsumptionOne(i, j);
      }
    }
  }

  @Test public void testUnif() {
    int i = 7;
    int j = 7;
    if (i > 0) {
      testUnifiableOne(i, j);
    }
  }

  public void testUnifiableOne(int i, int j) {
    logger = LoggerFactory.getLogger("testUnifiable");
    boolean result = afs[i].unifiable(bfs[j]);
    // compensate incomplete cycle check
    if (afs[i].checkCycles() || bfs[j].checkCycles()) result = false;
    if (result != unifResults[j + base.length * i]) {
      logger.info((unifResults[j + base.length * i] ? "" : "not ") +
          "unifiable: " + i + " + " + j + " : " + result);
      //if (DISPLAY) TFSDisplay.displayAndWait(afs[i], bfs[j]);
    }
    assertEquals("" + i + ":" + j, unifResults[j + base.length * i], result);
  }

  @Test public void testUnifiable() {
    for (int i = 0; i < base.length; ++i) {
      for (int j = 0; j < base.length; ++j) {
        testUnifiableOne(i, j);
      }
    }
  }

  public void testUnificationOne(int i, int j) {
    logger = LoggerFactory.getLogger("testUnification");
    TFS result = afs[i].unifyFS(bfs[j]);
    if ((result != null) != unifResults[j + base.length * i]) {
      logger.info((unifResults[j + base.length * i] ? "" : "not ") +
          "unifiable: " + i + " + " + j + " : " + result);
      //if (DISPLAY) TFSDisplay.displayAndWait(afs[i], bfs[j]);
    }
    else {
      if (result != null) {
        boolean ok = (
            (result.subsumesBi(afs[i]) & DagNode.ARG_MORE_GENERAL) != 0 &&
            (result.subsumesBi(bfs[j]) & DagNode.ARG_MORE_GENERAL) != 0);
        if (!ok) {
          logger.info("Unification result questionable " + i + " + " + j);
          // if (DISPLAY) TFSDisplay.displayAndWait(afs[i], bfs[j], result);
        }
        assertTrue(""+i+" "+j, ok);
      }
    }
  }


  @Test public void testUnification() {
    for (int i = 0; i < base.length; ++i) {
      for (int j = 0; j < base.length; ++j) {
        testUnificationOne(i, j);
      }
    }
  }

  private List<List<Short>> getPermutations(short[] set) {
    int pow = 1 >> set.length - 1; // 2 ^ set.length - 1
    List<List<Short>> result = new ArrayList<List<Short>>(pow);
    if (set.length == 1) {
      List<Short> perm = new ArrayList<Short>(1);
      perm.add(set[0]);
      result.add(perm);
      return result;
    }
    short[] subSet = new short[set.length - 1];
    for (short i = 0; i < set.length; ++i) {
      int subIndex = 0;
      for (int j = 0; j < set.length; ++j) {
        if (i != j) {
          subSet[subIndex++] = set[j];
        }
      }
      List<List<Short>> subPerms = getPermutations(subSet);
      for (List<Short> subPerm : subPerms) {
        subPerm.add(Short.valueOf(set[i]));
        result.add(subPerm);
      }
    }
    return result;
  }

  @Test public void testMultipleUnificationWithoutCopy() {
    int howmuch = 6;
    DagNode[] dags = new DagNode[howmuch];
    short[] indices = new short[howmuch];
    for (short i = 0; i < dags.length; ++i) {
      indices[i] = i;
      dags[i] = new DagNode(FSGrammar.TOP_TYPE);
      dags[i].addEdge(i, new DagNode(gram.nullTypeId));
    }
    DagNode reference = new DagNode(FSGrammar.TOP_TYPE);
    for (short i = 0; i < dags.length; ++i) {
      reference.addEdge(i, new DagNode(gram.nullTypeId));
    }
    List<List<Short>> permutations = getPermutations(indices);
    /*
    List<List<Short>> permutations = new ArrayList<List<Short>>(1);
    short[] perm = { 3, 2, 1, 0 };
    List<Short> permList = new ArrayList<Short>(4);
    for (int i = 0; i < perm.length; ++i){
      permList.add(perm[i]);
    }
    permutations.add(permList);
    */
    for (List<Short> permutation : permutations) {
      DagNode res = dags[permutation.get(0)];
      for (short i : permutation.subList(1, permutation.size())) {
        res.unifyOnly(dags[i]);
      }
      res = res.copyResult();
      assertEquals("Permutation: " + permutation, reference, res);
    }
  }

  private boolean testUnificationPartialHelper(int nr,
      TFS arg1, TFS arg2, TFS givenResult) {
    logger = LoggerFactory.getLogger("testUnifier");
    TFS result = arg1.unifyFS(arg2);
    boolean ok = (result.subsumesBi(givenResult) ==
      (DagNode.ARG_MORE_GENERAL | DagNode.THIS_MORE_GENERAL));
    if (!ok) {
      /*if (DISPLAY) TFSDisplay.displayAndWait(true,
          "UnifRes_"+ nr, result,
          "GivenRes_"+ nr, givenResult,
          null, null);
      */
      logger.error(description[nr] + " questionable ");
      logger.error("arg1: " + arg1);
      logger.error("arg2: " + arg2);
      logger.error("gres: " + givenResult);
      logger.error("res:  " + result);
    }
    return ok;
  }

  public void testUnifierPartialOne(int i) {
    boolean fw = testUnificationPartialHelper(i/3, tfs[i], tfs[i+1], tfs[i+2]);
    boolean bw = testUnificationPartialHelper(i/3, tfs[i+1], tfs[i], tfs[i+2]);
    assertTrue(fw && bw);
  }

  @Test public void testUnifierPartial() {
    for (int i = 0; i < partTest.length; i += 3) {
      testUnifierPartialOne(i);
    }
  }

  @Test public void equalsTest() throws InvalidSyntaxException {
    TFS fs1 = TFS.fsFromString("[ *top* ARGS [ *cons* FIRST [ j ] REST [ *null* ] ] ]");
    TFS fs2 = TFS.fsFromString("[ *top* ARGS [ *cons* FIRST [ j ] REST [ *null* ] ] ]");
    assertEquals(fs1, fs2);
  }

  @Test public void cloneTest() throws InvalidSyntaxException {
    TFS fs1 = TFS.fsFromString("[ *top* ARGS [ *cons* FIRST [ j ] REST [ *null* ] ] ]");
    TFS fs2 = fs1.cloneFS();
    assertFalse(fs1 == fs2);
    assertEquals(fs1, fs2);
  }


  @Test public void copyResultTest() throws InvalidSyntaxException {
    TFS fs1 = TFS.fsFromString("[ *top* ARGS [ *cons* FIRST [ j ] REST [ *null* ] ] ]");
    TFS fs2 = fs1.copyResult();
    assertFalse(fs1 == fs2);
    assertEquals(fs1, fs2);
    String[] toDelete = { FSGrammar.ARGS_FEATURE_NAME };
    TFS fs3 = fs1.copyResult(DelDtrsMassager.newMassager(gram, toDelete));
    assertEquals(TFS.fsFromString("[ *top* ]"), fs3);
  }

  @Test public void getSubNodeTest() throws InvalidSyntaxException {
    TFS fs1 = TFS.fsFromString("[ *top* ARGS [ *cons* FIRST [ j ] REST [ *null* ] ] ]");
    TFS fs2 = TFS.fsFromString("[ j ]");
    assertEquals(fs2.dag(), fs1.getSubNode(
        Arrays.asList(
            new Short[] {DagNode.ARGS_FEATURE, DagNode.FIRST_FEATURE}).iterator()));
  }

  @Test public void testUnifyWithArg() throws InvalidSyntaxException {
    TFS fs1 = TFS.fsFromString("[ *top* ARGS [ *cons* FIRST [ j ] REST [ *null* ] ] ]");
    TFS fs2 = TFS.fsFromString("[ j ]");
    TFS fs3 = TFS.fsFromString("[ f ]");
    assertEquals(fs1, fs1.unifyFS(fs2, 0));
    assertTrue(fs1.unifyOnly(fs2, 0));
    assertNull(fs1.unifyFS(fs3, 0));
    assertFalse(fs1.unifyOnly(fs3, 0));
    assertNull(fs1.unifyFS(fs2, 1));
  }

  @Test public void testArity() throws InvalidSyntaxException {
    TFS fs1 = TFS.fsFromString("[ *top* ARGS [ *cons* FIRST [ j ] REST [ *null* ] ] ]");
    assertEquals(1, fs1.getArity());
  }

  @Test public void testGetNthArg() throws InvalidSyntaxException {
    TFS fs1 = TFS.fsFromString("[ *top* ARGS [ *cons* FIRST [ j ] REST [ *null* ] ] ]");
    TFS fs2 = TFS.fsFromString("[ j ]");
    assertEquals(fs2, fs1.getNthArg(0));
  }

  @Test(expected=InvalidSyntaxException.class)
  public void testInvalidSyntax() throws InvalidSyntaxException {
    @SuppressWarnings("unused")
    TFS fs1 = TFS.fsFromString("[ *top* ARGS *cons* FIRST [ j ] REST [ *null* ] ] ]");
  }

  @Test public void testCreationAndGetType() {
    TFS fs1 = new TFS(7);
    assertEquals(7, fs1.getType());
  }

  @Test public void testQC() throws InvalidSyntaxException {
    TFS fs1 = TFS.fsFromString("[ *cons*" +
        " FIRST [ j ]" +
        " REST [ *cons* FIRST [ *top* ARGS [ *null* ] ] REST [ f ] ] ]");
    int[] result = { DagNode.fsgrammar.getNumberForTypeName("*cons*"),
        DagNode.fsgrammar.getNumberForTypeName("j"),
        FSGrammar.TOP_TYPE, -1, -1 };
    assertEquals(TFS.getQCSize(), 5);
    for (int pos = 0; pos < TFS.getQCSize(); ++pos) {
      assertEquals("Position " + pos, result[pos], fs1.getQCType(pos));
    }
    DagNode[] qcv = fs1.getQCDagVector();
    for (int pos = 0; pos < TFS.getQCSize(); ++pos) {
      assertEquals("Position " + pos, result[pos],
          qcv[pos] == null ? -1 : qcv[pos].dereference().getNewType()
          );
    }
  }

  /* ENABLE ASSERTIONS FOR UNIT TESTS TO MAKE THIS WORK */
  @Test(expected=AssertionError.class)
  public void testQCAssert() throws InvalidSyntaxException {
    TFS fs1 = TFS.fsFromString("[ *top* ARGS [ *cons*" +
        " FIRST [ j ARGS [ *cons* ] ]" +
        " REST [ *cons* FIRST [ *null* ] REST [ f ] ] ] ]");
    fs1.setQCVector(0);
    // only caught by an assertion
    fs1.getQCType(6);
  }

  @Test public void testArgQC() throws InvalidSyntaxException {
    TFS fs1 = TFS.fsFromString("[ *top* ARGS [ *cons*" +
        " FIRST [ j ARGS [ *cons* ] ]" +
        " REST [ *cons* FIRST [ *null* ] REST [ f ] ] ] ]");
    fs1.setQCVector(0);
    int[] argResult = { DagNode.fsgrammar.getNumberForTypeName("j"), -1, -1,
        DagNode.fsgrammar.getNumberForTypeName("*cons*"), -1 };
    assertEquals(TFS.getQCSize(), 5);
    for (int pos = 0; pos < TFS.getQCSize(); ++pos) {
      assertEquals("Position " + pos, argResult[pos], fs1.getArgQCType(pos));
    }
  }

  @Test public void testArgQCCompatible() throws InvalidSyntaxException {
    TFS fs1 = TFS.fsFromString("[ *top* ARGS[*cons*" +
        " FIRST [ j ARGS [*cons*]]" +
        " REST [*cons* FIRST [*null*] REST [f]]]]");
    TFS fs2 = TFS.fsFromString("[ j ]");
    TFS fs3 = TFS.fsFromString("[ f ARGS [ *cons* ] ]");
    TFS fs4 = TFS.fsFromString("[ *list* ARGS [ *top* ] ]");
    TFS fs5 = TFS.fsFromString("[ *cons* ]");
    fs1.setQCVector(0);
    assertTrue(fs1.qcCompatible(fs2));
    assertFalse(fs1.qcCompatible(fs3));
    fs1.setQCVector(1);
    assertTrue(fs1.qcCompatible(fs4));
    assertFalse(fs1.qcCompatible(fs5));
  }

  @Test public void testPrinting() throws InvalidSyntaxException {
    String fs1String = "[*top* ARGS[*cons*" +
        " FIRST[j ARGS[*cons*]]" +
        " REST[*cons* FIRST[*null*] REST[f]]]]";
    TFS fs1 = TFS.fsFromString(fs1String);
    assertEquals(fs1String, fs1.toString());
  }

  @Test public void testHash() throws InvalidSyntaxException {
    TFS fs1 = TFS.fsFromString("[ *top* ARGS [ *cons*" +
        " FIRST [ j ARGS [ *cons* ] ]" +
        " REST [ *cons* FIRST [ *null* ] REST [ f ] ] ] ]");
    TFS fs2 = TFS.fsFromString("[ *top* ARGS [ *cons*" +
        " FIRST [ j ARGS [ *cons* ] ]" +
        " REST [ *cons* FIRST [ *null* ] REST [ f ] ] ] ]");
    HashSet<TFS> set = new HashSet<TFS>();
    set.add(fs1);
    assertTrue(set.contains(fs2));
  }

  @Test public void createRestrictorTest() throws InvalidSyntaxException {
    TFS fs1 = TFS.fsFromString("[ *top* ARGS [ rstr_no" +
        " FIRST # 1 [ rstr_no ARGS [ rstr_del ] REST # 1 ]" +
        " REST [ rstr_no FIRST [ rstr_no ] REST [ rstr_del ] ] ] ]");
    TFS fs2 = TFS.fsFromString("[ *top* ARGS [ g" +
        " FIRST # 1 [ g ARGS [ f ] REST # 1 ]" +
        " REST [ g FIRST [ g ] REST [ f ] ] ] ]");
    TFS restr = fs1.getRestrictorDag();
    assertEquals(fs2, restr);
  }

  @Test public void createRestrictorTest2() throws InvalidSyntaxException {
    TFS fs1 = TFS.fsFromString("[ *top* ARGS [ \"rstr_no\"" +
        " FIRST # 1 [ \"rstr_no\" ARGS [ \"rstr_del\" ] REST # 1 ]" +
        " REST [ \"rstr_no\" FIRST [ \"rstr_no\" ]" +
        "                    REST [ \"rstr_del\" ] ] ] ]");
    TFS fs2 = TFS.fsFromString("[ *top* ARGS [ g" +
        " FIRST # 1 [ g ARGS [ f ] REST # 1 ]" +
        " REST [ g FIRST [ g ] REST [ f ] ] ] ]");
    TFS restr = fs1.getRestrictorDag();
    assertEquals(fs2, restr);
  }

  protected static String restr_dags[] = {
    "[ *top* ARGS [ *cons* ]\n"+
    "  FIRST [ *top* FIRST # 1 [ *top* ARGS [ *top* ] ] ARGS # 1 REST # 1 ]\n"+
    "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
    "                FIRST [ *top* REST [ *cons* ] ]\n" +
    "                REST [ *cons* FIRST [ *top* ARGS [ *top* ] ] ] ] ]\n"
  };

  protected static String restr_results[] = {
    "[ *top* FIRST [ *top* FIRST # 1 [ *top* ARGS [ *top* ] ] REST # 1 ]"+
    "  REST  [ *top* ARGS #2 [ *cons* ]" +
    "                FIRST [ *top* REST [ *cons* ] ] ] ]"
  };

  @Test public void useRestrictorTest() throws InvalidSyntaxException {
    TFS[] restrs = {
        TFS.fsFromString("[ *top* " +
            " FIRST [ rstr_no ARGS [ rstr_del ] ]" +
            " REST [ rstr_no FIRST [ rstr_no ] REST [ rstr_del ] ] ]"),
        TFS.fsFromString("[ *top* " +
            " FIRST [ \"rstr_no\" ARGS [ \"rstr_del\" ] ]" +
            " REST [ \"rstr_no\" FIRST [ \"rstr_no\" ]" +
            "                    REST [ \"rstr_del\" ] ] ]")
    };
    for (TFS rfs : restrs) {
      TFS restr = rfs.getRestrictorDag();
      int i = 0;
      for (String fs : restr_dags) {
        TFS fsIn = TFS.fsFromString(fs);
        TFS fsExpected = TFS.fsFromString(restr_results[i++]);
        TFS fsOut = fsIn.cloneFS();
        fsOut.restrict(restr);
        // TFSDisplay.displayAndWait(restr, fsIn, fsOut);
        assertEquals("" + (i-1), fsExpected, fsOut);
      }
    }
  }

  @Test public void copyAndRestrictTest() throws InvalidSyntaxException {
    TFS[] restrs = {
        TFS.fsFromString("[ *top* " +
            " FIRST [ rstr_no ARGS [ rstr_del ] ]" +
            " REST [ rstr_no FIRST [ rstr_no ] REST [ rstr_del ] ] ]"),
        TFS.fsFromString("[ *top* " +
            " FIRST [ \"rstr_no\" ARGS [ \"rstr_del\" ] ]" +
            " REST [ \"rstr_no\" FIRST [ \"rstr_no\" ]" +
            "                    REST [ \"rstr_del\" ] ] ]")
    };
    for (TFS rfs : restrs) {
      TFS restr = rfs.getRestrictorDag();
      FSMassager m = FullMassager.newMassager(gram, null, restr);
      int i = 0;
      for (String fs : restr_dags) {
        TFS fsIn = TFS.fsFromString(fs);
        TFS fsExpected = TFS.fsFromString(restr_results[i++]);
        DagNode.invalidate();
        TFS fsOut = fsIn.copyResult(restr);
        // TFSDisplay.displayAndWait(restr, fsIn, fsOut);
        assertEquals("" + (i-1), fsExpected, fsOut);
      }
    }
  }

  @Test public void glbSaveTest() throws IOException {
    int noTypes = gram.getNoOfTypes();
    for (int i = 1; i < noTypes; ++i) {
      for (int j = i + 1; j < noTypes; ++j) {
        gram.unifyTypes(i, j);
      }
    }
    // now the cache should be filled completely
    assertEquals(((noTypes - 2) * (noTypes - 1)) / 2, gram._glbCache.size());
    FileWriter out = new FileWriter("/tmp/glbcache");
    gram.dumpGlbCache(out);
    out.close();
    TLongIntMap saveCache = gram._glbCache;
    gram._glbCache = new TLongIntHashMap();
    FileReader in = new FileReader("/tmp/glbcache");
    TLongIntMap cache = gram.undumpGlbCache(in);
    assertEquals(cache, saveCache);
  }

}
