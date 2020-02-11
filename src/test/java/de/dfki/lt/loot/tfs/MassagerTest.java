package de.dfki.lt.loot.tfs;

import static org.junit.Assert.*;

import java.io.File;

import org.junit.BeforeClass;
import org.junit.Test;

import de.dfki.lt.loot.tfs.io.InvalidSyntaxException;

public class MassagerTest {
  private static FSGrammar gram;

  @BeforeClass public static void setUp() {
    File resourceDir = UnifTest.getTestResourceDir();

    gram = new FSGrammar(
        new File(resourceDir, "minimal/uniftest.grm").getAbsolutePath());

  }

  @Test
  public void createRestrictorTest1() throws InvalidSyntaxException {
    TFS fs1 = TFS.fsFromString("[ *top* ARGS [ \"rstr_no\"" +
        " FIRST # 1 [ \"rstr_no\" ARGS [ \"rstr_del\" ] REST # 1 ]" +
        " REST [ \"rstr_no\" FIRST [ \"rstr_no\" ]" +
        "                    REST [ \"rstr_del\" ] ] ] ]");
    FullMassager f = FullMassager.newMassager(gram, null, fs1);
    assertNotNull(f);
    System.out.println(f);
  }

  @Test
  public void createRestrictorTest2() throws InvalidSyntaxException {
    TFS fs1 = TFS.fsFromString("[ *top* ARGS [ \"rstr_no,*top*\"" +
        " FIRST # 1 [ \"rstr_no\" ARGS [ \"rstr_del\" ] REST # 1 ]" +
        " REST [ \"rstr_keep\" FIRST [ \"rstr_no\" ]" +
        "                    REST [ \"rstr_del\" ] ] ] ]");
    FullMassager f = FullMassager.newMassager(gram, null, fs1);
    assertNotNull(f);
  }

  @Test
  public void testDefault() throws InvalidSyntaxException{
    String restr_dags[] = {
        "[ *top* ARGS [ *cons* ]\n"+
        "  FIRST [ *top* FIRST # 1 [ *top* ARGS [ *top* ] ] ARGS # 1 REST # 1 ]\n"+
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                FIRST [ *top* REST [ *cons* ] ]\n" +
        "                REST [ *cons* FIRST [ *top* ARGS [ *top* ] ] ] ] ]\n"
      };

    String restr_results[] = {
      "[ *top* ARGS [ *cons* ] FIRST [ *top* FIRST [ *top* ] ] ]"
    };

    TFS fs1 = TFS.fsFromString(
        "[ rstr_keep ARGS [ rstr_keep ] FIRST [ rstr_keep FIRST [ rstr_keep ] ] ]");
    FullMassager f = FullMassager.newMassager(gram, null, fs1);
    TFS in = TFS.fsFromString(restr_dags[0]);
    TFS fs2 = f.copyRestrict(in);
    TFS out = TFS.fsFromString(restr_results[0]);
    assertEquals(out, fs2);
  }

  @Test
  public void testDefaultRecursive() throws InvalidSyntaxException{
    String inDag =
        "[*top* ARGS [*cons* FIRST #1 [ *cons* FIRST [*top* ARGS [ *top* ]]"
        + " ARGS [foo]] REST [*cons* FIRST [ foo REST [ *cons* ] ARGS [*top*]]"
        + " REST #1]]]";

    String outDag = "[*top* ARGS [*cons* FIRST #1 [*cons* ARGS [foo]] "
        + "REST [*cons* FIRST [foo ARGS [*top*]] REST #1]]]";


    TFS fs1 = TFS.fsFromString(
        "#1 [ rstr_keep ARGS #2 [ rstr_keep FIRST #1 REST #2 ]]");
    FullMassager f = FullMassager.newMassager(gram, null, fs1);
    TFS in = TFS.fsFromString(inDag);
    TFS fs2 = f.copyRestrict(in);
    TFS out = TFS.fsFromString(outDag);
    System.out.println(f);
    assertEquals(out, fs2);
  }

  @Test
  public void testKeep() throws InvalidSyntaxException{
    String restr_dags[] = {
        "[ *top* ARGS [ *cons* ]\n"+
        "  FIRST [ *top* FIRST # 1 [ *top* ARGS [ *top* ] ] ARGS # 1 REST # 1 ]\n"+
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                FIRST [ *top* REST [ *cons* ] ]\n" +
        "                REST [ *cons* FIRST [ *top* ARGS [ *top* ] ] ] ] ]\n"
      };

    String restr_results[] = {
      "[ *top* ARGS [ *cons* ] FIRST [ *top* FIRST [ *top* ] ] ]"
    };

    TFS fs1 = TFS.fsFromString(
        "[ rstr_keep ARGS [ rstr_keep ] FIRST [ rstr_keep FIRST [ rstr_keep ] ] ]");
    FullMassager f = FullMassager.newMassager(gram, null, fs1);
    TFS in = TFS.fsFromString(restr_dags[0]);
    TFS fs2 = f.copyRestrict(in);
    TFS out = TFS.fsFromString(restr_results[0]);
    assertEquals(out, fs2);
  }

  @Test
  public void testNo() throws InvalidSyntaxException{
    String restr_dags[] = {
        "[ *top* ARGS [ *cons* ]\n"+
        "  FIRST [ *top* FIRST # 1 [ *top* ARGS [ *top* ] ] ARGS # 1 REST # 1 ]\n"+
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                FIRST [ *top* REST [ *cons* ] ]\n" +
        "                REST [ *cons* FIRST [ *top* ARGS [ *top* ] ] ] ] ]\n"
      };

    String restr_results[] = {
        "[ *top* "
        + "ARGS [ *cons* ]"
        + "FIRST [ *top* FIRST [ *top* ARGS [ *top* ] ] ]"+
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                FIRST [ *top* REST [ *cons* ] ]\n" +
        "                REST [ *cons* FIRST [ *top* ARGS [ *top* ] ] ] ] ]\n"
    };

    TFS fs1 = TFS.fsFromString(
        "[ rstr_no ARGS [ rstr_keep ] FIRST [ rstr_keep FIRST [ rstr_no ] ] ]");
    FullMassager f = FullMassager.newMassager(gram, null, fs1);
    TFS in = TFS.fsFromString(restr_dags[0]);
    TFS fs2 = f.copyRestrict(in);
    TFS out = TFS.fsFromString(restr_results[0]);
    assertEquals(out, fs2);
  }

  @Test
  public void testDel() throws InvalidSyntaxException{
    String restr_dags[] = {
        "[ *top* ARGS [ *cons* ]\n"+
        "  FIRST [ *top* FIRST # 1 [ *top* ARGS [ *top* ] ] ARGS # 1 REST # 1 ]\n"+
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                FIRST [ *top* REST [ *cons* ] ]\n" +
        "                REST [ *cons* FIRST [ *top* ARGS [ *top* ] ] ] ] ]\n"
      };

    String restr_results[] = {
        "[ *top* "
        + "FIRST [ *top* ARGS #1 [ *top* ARGS [ *top* ] ] REST # 1 ]"+
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                FIRST [ *top* REST [ *cons* ] ]\n" +
        "                REST [ *cons* FIRST [ *top* ARGS [ *top* ] ] ] ] ]\n"
    };

    TFS fs1 = TFS.fsFromString(
        "[ rstr_no ARGS [ rstr_del ] FIRST [ rstr_no FIRST [ rstr_del ] ] ]");
    FullMassager f = FullMassager.newMassager(gram, null, fs1);
    TFS in = TFS.fsFromString(restr_dags[0]);
    TFS fs2 = f.copyRestrict(in);
    TFS out = TFS.fsFromString(restr_results[0]);
    assertEquals(out, fs2);
  }

  @Test
  public void testDeletedFeatures() throws InvalidSyntaxException{
    String restr_dags[] = {
        "[ *top* ARGS [ *cons* ]\n"+
        "  FIRST [ *top* FIRST # 1 [ *top* ARGS [ *top* ] ] ARGS # 1 REST # 1 ]\n"+
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                FIRST [ *top* REST [ *cons* ] ]\n" +
        "                REST [ *cons* FIRST [ *top* ARGS [ *top* ] ] ] ] ]\n"
      };

    String restr_results[] = {
        "[ *top* \n"+
        "  FIRST [ *top* FIRST # 1 [ *top* ] REST # 1 ]\n"+
        "  REST  [ *top* \n" +
        "                FIRST [ *top* REST [ *cons* ] ]\n" +
        "                REST [ *cons* FIRST [ *top*  ] ] ] ]\n"

    };

    //TFS fs1 = TFS.fsFromString(
    //    "[ rstr_no ARGS [ rstr_del ] FIRST [ rstr_no FIRST [ rstr_del ] ] ]");

    String[] ftd = { "ARGS" };
    FullMassager f = FullMassager.newMassager(gram, ftd, null);

    TFS in = TFS.fsFromString(restr_dags[0]);
    TFS fs2 = f.copyRestrict(in);
    TFS out = TFS.fsFromString(restr_results[0]);
    assertEquals(out, fs2);
  }

  @Test
  public void testDeletedFeatures2() throws InvalidSyntaxException{
    String restr_dags[] = {
        "[ *top* ARGS [ *cons* ]\n"+
        "  FIRST [ *top* FIRST # 1 [ *top* ARGS [ *top* ] ] ARGS # 1 REST # 1 ]\n"+
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                FIRST [ *top* REST [ *cons* ] ]\n" +
        "                REST [ *cons* FIRST [ *top* ARGS [ *top* ] ] ] ] ]\n"
      };

    String restr_results[] = {
        "[ *top* \n"+
        "  FIRST [ *top* FIRST # 1 [ *top* ] ] ]\n"
    };

    //TFS fs1 = TFS.fsFromString(
    //    "[ rstr_no ARGS [ rstr_del ] FIRST [ rstr_no FIRST [ rstr_del ] ] ]");

    String[] ftd = { "ARGS", "REST" };
    FullMassager f = FullMassager.newMassager(gram, ftd, null);

    TFS in = TFS.fsFromString(restr_dags[0]);
    TFS fs2 = f.copyRestrict(in);
    TFS out = TFS.fsFromString(restr_results[0]);
    assertEquals(out, fs2);
  }

  @Test
  public void testDelAndFeatures() throws InvalidSyntaxException{
    String restr_dags[] = {
        "[ *top* ARGS [ *cons* ]\n"+
        "  FIRST [ *top* FIRST # 1 [ *top* ARGS [ *top* ] ] ARGS # 1 REST # 1 ]\n"+
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                FIRST [ *top* REST [ *cons* ] ]\n" +
        "                REST [ *cons* FIRST [ *top* ARGS [ *top* ] ] ] ] ]\n"
      };

    String restr_results[] = {
        "[ *top* "
        + "FIRST [ *top* ARGS #1 [ *top* ARGS [ *top* ] ] ] ]"
    };

    TFS fs1 = TFS.fsFromString(
        "[ rstr_no ARGS [ rstr_del ] FIRST [ rstr_no FIRST [ rstr_del ] ] ]");
    String[] ftd = { "REST" };
    FullMassager f = FullMassager.newMassager(gram, ftd, fs1);
    TFS in = TFS.fsFromString(restr_dags[0]);
    TFS fs2 = f.copyRestrict(in);
    TFS out = TFS.fsFromString(restr_results[0]);
    assertEquals(out, fs2);
  }

  @Test
  public void testDelAndFeatures2() throws InvalidSyntaxException{
    String restr_dags[] = {
        "[ *top* ARGS [ *cons* ]\n"+
        "  FIRST [ *top* FIRST # 1 [ *top* ARGS [ *top* ] ] ARGS # 1 REST # 1 ]\n"+
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                FIRST [ *top* REST [ *cons* ] ]\n" +
        "                REST [ *cons* FIRST [ *top* ARGS [ *top* ] ] ] ] ]\n"
      };

    String restr_results[] = {
        "[ *top* " +
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                REST [ *cons* ] ] ]\n"
    };

    TFS fs1 = TFS.fsFromString(
        "[ rstr_no ARGS [ rstr_del ] FIRST [ rstr_no FIRST [ rstr_del ] ] ]");
    String[] ftd = { "FIRST" };
    FullMassager f = FullMassager.newMassager(gram, ftd, fs1);
    TFS in = TFS.fsFromString(restr_dags[0]);
    TFS fs2 = f.copyRestrict(in);
    TFS out = TFS.fsFromString(restr_results[0]);
    assertEquals(out, fs2);
  }

  @Test
  public void testGeneralizeTypeNoRestr() throws InvalidSyntaxException{
    String restr_dags[] = {
        "[ *top* ARGS [ *cons* ]\n"+
        "  FIRST [ *top* FIRST # 1 [ *top* ARGS [ *top* ] ] ARGS # 1 REST # 1 ]\n"+
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                FIRST [ *top* REST [ *cons* ] ]\n" +
        "                REST [ *cons* FIRST [ *top* ARGS [ *top* ] ] ] ] ]\n"
      };

    String restr_results[] = {
        "[ *top* ARGS [ *top* ] " +
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                REST [ *cons* ] ] ]\n"
    };

    TFS fs1 = TFS.fsFromString(
        "[ rstr_no ARGS [ *top* ] FIRST [ rstr_no FIRST [ rstr_del ] ] ]");
    String[] ftd = { "FIRST" };
    FullMassager f = FullMassager.newMassager(gram, ftd, fs1);
    TFS in = TFS.fsFromString(restr_dags[0]);
    TFS fs2 = f.copyRestrict(in);
    TFS out = TFS.fsFromString(restr_results[0]);
    assertEquals(out, fs2);
  }

  @Test
  public void testGeneralizeTypeRestr() throws InvalidSyntaxException{
    String restr_dags[] = {
        "[ *top* ARGS [ *cons* ]\n"+
        "  FIRST [ *top* FIRST # 1 [ *top* ARGS [ *top* ] ] ARGS # 1 REST # 1 ]\n"+
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                FIRST [ *top* REST [ *cons* ] ]\n" +
        "                REST [ *cons* FIRST [ *top* ARGS [ *top* ] ] ] ] ]\n"
      };

    String restr_results[] = {
        "[ *top* " +
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                REST [ *top* ] ] ]\n"
    };

    TFS fs1 = TFS.fsFromString(
        "[ rstr_no ARGS [ rstr_del ] FIRST [ rstr_del ] " +
                  "REST [ rstr_keep ARGS [ rstr_keep ] REST [ \"rstr_keep,*top*\" ] ] ]");
    // String[] ftd = { "FIRST" };
    FullMassager f = FullMassager.newMassager(gram, null, fs1);
    TFS in = TFS.fsFromString(restr_dags[0]);
    TFS fs2 = f.copyRestrict(in);
    TFS out = TFS.fsFromString(restr_results[0]);
    assertEquals(out, fs2);
  }

  @Test
  public void testGeneralizeTypeMulti() throws InvalidSyntaxException{
    String restr_dags[] = {
        "[ *top* ARGS [ *cons* ]\n"+
        "  FIRST [ *top* FIRST # 1 [ *top* ARGS [ *top* ] ] ARGS # 1 REST # 1 ]\n"+
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                FIRST [ *top* REST [ *cons* ] ]\n" +
        "                REST [ *cons* FIRST [ *top* ARGS [ *top* ] ] ] ] ]\n"
      };

    String restr_results[] = {
        "[ *top* " +
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                REST [ *list* ] ] ]\n"
    };

    TFS fs1 = TFS.fsFromString(
        "[ rstr_no ARGS [ rstr_del ] FIRST [ rstr_del ] " +
                  "REST [ rstr_keep ARGS [ rstr_keep ] REST [ \"rstr_keep,*list*,*top*\" ] ] ]");
    // String[] ftd = { "FIRST" };
    FullMassager f = FullMassager.newMassager(gram, null, fs1);
    TFS in = TFS.fsFromString(restr_dags[0]);
    TFS fs2 = f.copyRestrict(in);
    TFS out = TFS.fsFromString(restr_results[0]);
    assertEquals(out, fs2);
  }

  @Test
  public void testGeneralizeTypeMulti2() throws InvalidSyntaxException{
    String restr_dags[] = {
        "[ *top* ARGS [ *cons* ]\n"+
        "  FIRST [ *top* FIRST # 1 [ *top* ARGS [ *top* ] ] ARGS # 1 REST # 1 ]\n"+
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                FIRST [ *top* REST [ *cons* ] ]\n" +
        "                REST [ *cons* FIRST [ *top* ARGS [ *top* ] ] ] ] ]\n"
      };

    String restr_results[] = {
        "[ *top* " +
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                REST [ *top* ] ] ]\n"
    };

    TFS fs1 = TFS.fsFromString(
        "[ rstr_no ARGS [ rstr_del ] FIRST [ rstr_del ] " +
                  "REST [ rstr_keep ARGS [ rstr_keep ] REST [ \"rstr_keep,*diff-list*,*top*\" ] ] ]");
    // String[] ftd = { "FIRST" };
    FullMassager f = FullMassager.newMassager(gram, null, fs1);
    TFS in = TFS.fsFromString(restr_dags[0]);
    TFS fs2 = f.copyRestrict(in);
    TFS out = TFS.fsFromString(restr_results[0]);
    assertEquals(out, fs2);
  }

  @Test
  public void testGeneralizeTypeMulti3() throws InvalidSyntaxException{
    String restr_dags[] = {
        "[ *top* ARGS [ *cons* ]\n"+
        "  FIRST [ *top* FIRST # 1 [ *top* ARGS [ *top* ] ] ARGS # 1 REST # 1 ]\n"+
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                FIRST [ *top* REST [ *cons* ] ]\n" +
        "                REST [ *cons* FIRST [ *top* ARGS [ *top* ] ] ] ] ]\n"
      };

    String restr_results[] = {
        "[ *top* " +
        "  REST  [ *top* ARGS #2 [ *cons* ]\n" +
        "                REST [ *cons* ] ] ]\n"
    };

    TFS fs1 = TFS.fsFromString(
        "[ rstr_no ARGS [ rstr_del ] FIRST [ rstr_del ] " +
                  "REST [ rstr_keep ARGS [ rstr_keep ] REST [ \"rstr_keep,*diff-list*,f\" ] ] ]");
    // String[] ftd = { "FIRST" };
    FullMassager f = FullMassager.newMassager(gram, null, fs1);
    TFS in = TFS.fsFromString(restr_dags[0]);
    TFS fs2 = f.copyRestrict(in);
    TFS out = TFS.fsFromString(restr_results[0]);
    assertEquals(out, fs2);
  }

  @Test
  public void testCyclicRestrictorCreate() throws InvalidSyntaxException{
    String cyclrest =
        "[ rstr_keep ARGS #1 [ rstr_keep FIRST [ rstr_keep ] REST #1 ] ]";
    TFS cr = TFS.fsFromString(cyclrest);
    FullMassager f = FullMassager.newMassager(gram, null, cr);
    assertNotNull(f);
  }

  @Test
  public void testCyclicRestrictor() throws InvalidSyntaxException{
    String cyclrest =
        "[ rstr_keep ARGS #1 [ rstr_keep FIRST [ rstr_keep ] REST #1 ] ]";
    TFS cr = TFS.fsFromString(cyclrest);

    String inDag =
        "[ *top* ARGS [*top* ARGS [*top* REST [*top*]] "
        + "     FIRST [*top* REST [*top*]] "
        + "     REST [*top* FIRST [*top* REST [*top*]] ARGS [*top* REST [*top*]]]] "
        + "REST [*top*]]";

    String outDag =
        "[ *top* ARGS [ *top* FIRST [*top*] REST [*top* FIRST [*top*]]]]";

    TFS in = TFS.fsFromString(inDag);
    TFS out = TFS.fsFromString(outDag);

    FullMassager f = FullMassager.newMassager(gram, null, cr);
    TFS res = f.copyRestrict(in);
    assertEquals(out, res);
  }


  @Test
  public void testCyclicRestrictor2() throws InvalidSyntaxException{
    String cyclrest =
        "[rstr_keep ARGS #1 [rstr_keep LIST #2 [rstr_keep FIRST #1 REST #2]]]";
    TFS cr = TFS.fsFromString(cyclrest);

    String inDag = "[*top* ARGS [*top* LIST [*top* FIRST [*top* LIST [*top*] "
        + "FIRST[*top*] REST [*top*]] REST [*top* FIRST [*top* LIST [*top*] "
        + "FIRST[*top*] REST [*top*]] REST [*top*]]]]]";

    String outDag = "[*top* ARGS [*top* LIST [*top* FIRST [*top* LIST [*top*] ]"
        + "REST  [*top* FIRST [*top* LIST [*top*] ] REST [*top*]]]]]";

    TFS in = TFS.fsFromString(inDag);
    TFS out = TFS.fsFromString(outDag);

    FullMassager f = FullMassager.newMassager(gram, null, cr);
    TFS res = f.copyRestrict(in);
    assertEquals(out, res);
  }
}
