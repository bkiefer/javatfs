package de.dfki.lt.loot.tfs;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.Writer;
import java.util.Iterator;
import java.util.List;

import joptsimple.OptionException;
import joptsimple.OptionParser;
import joptsimple.OptionSet;

import org.apache.log4j.BasicConfigurator;
import org.apache.log4j.Logger;

import de.dfki.lt.loot.tfs.io.EdgeConsumer;
import de.dfki.lt.loot.tfs.io.SimpleTfsConsumer;
import de.dfki.lt.loot.tfs.io.TfsConsumer;

public class TFSRunner {

  private static Logger logger = Logger.getLogger("MassTest");

  private FSGrammar gram;

  private int maxFS;
  private int interval;

  public TFSRunner(String grammarFileName, int max, int intv, int save) {
    gram = new FSGrammar(grammarFileName);
    maxFS = max;
    interval = intv;
  }

  private static final String[] featuresToDelete = {
    "STEM", "ARGS"
    /*
    "CONT", "C-CONT",
    "--COMPKEY", "--OCOMPKEY", "--+COMPKEY", "--+OCOMPKEY",
    "STEM",
    //"LKEYS"
    //"KEYREL", "ALTKEYREL", "ALT2KEYREL"
    "PRED", "CARG", "CFROM", "CTO"
    */
    };

  /*
   * void setupSubsumptionMatrix() { int forward = 0, backward = 0, equals = 0,
   * total = 0; subsumes = new BitSet[tfsList.size()]; for (int i = 0; i <
   * tfsList.size(); ++i) { TFS first = tfsList.get(i); for (int j = 0; j < i;
   * ++j) { if (true || i == enterList[0] || j == enterList[0] || i ==
   * testList[0] || j == testList[0]) { total++; int result =
   * first.subsumesBi(tfsList.get(j)); if (result == TFS.THIS_MORE_GENERAL) {
   * setSubsumes(i, j); forward++; } if (result == TFS.ARG_MORE_GENERAL) {
   * setSubsumes(j, i); backward++; } if (result == TFS.ARG_MORE_GENERAL +
   * TFS.THIS_MORE_GENERAL) { equals++; } } } setSubsumes(i, i); }
   * logger.info("Finished subsumption matrix[" + total + "]; eq: " + equals +
   * " fw: " + forward + " bw: " + backward); }
   *
   * FSIndex addFStoIndex(int toAdd, HashMap<Integer, Integer> TFSInIndex) {
   * FSIndex fsi = new FSIndex(); if (enterList == null) { enterList = new
   * int[toAdd]; for (int i = 0; i < toAdd; ++i) { int j; do { j = (int)
   * Math.floor(Math.random() * tfsList.size()); } while (TFSInIndex.get(j) !=
   * null && !fsi.contains(tfsList.get(j))); enterList[i] = j;
   * fsi.add(tfsList.get(j)); TFSInIndex.put(j, i); }
   * System.out.println("enterlist\n{ 0, "); for (int i : enterList)
   * System.out.print(i + ", "); System.out.println("}"); } else { fsi = new
   * FSIndex(); int i = 0; for (int j : enterList) { if (j >= tfsList.size())
   * break; fsi.add(tfsList.get(j)); TFSInIndex.put(j, i); // j is represented
   * by the i'th bit of the vector i++; } } return fsi; }
   *
   * private static int[] fillRandom(int howmany, int noTFS) { int[] result =
   * new int[howmany]; for (int i = 0; i < howmany; ++i) { result[i] = (int)
   * Math.floor(Math.random() * noTFS); } System.out.println("testlist\n{ 0, ");
   * for (int i : result) System.out.print(i + ", "); System.out.println("}");
   * return result; }
   *
   * * add random indexFactor x #TFS structures to the index and do testFactor x
   * #TFS random tests for subsumption.
   *
   * @param indexFactor
   *
   * @param testFactor
   *
   * void testSubsumption(double indexFactor, double testFactor) { int noTFS =
   * tfsList.size(); HashMap<Integer, Integer> TFSInIndex = new HashMap<Integer,
   * Integer>(); FSIndex fsi = addFStoIndex((int) (noTFS * indexFactor),
   * TFSInIndex); logger.info("Added " + enterList.length + " FS to index"); int
   * success = 0, failure = 0; if (testList == null) { testList =
   * fillRandom((int) (noTFS * testFactor), noTFS); } for (int i = 0; i <
   * testList.length; ++i) { int j = testList[i]; BitSet result =
   * fsi.isSubsumedBy(tfsList.get(j)); for (Map.Entry<Integer, Integer> pair :
   * TFSInIndex.entrySet()) { // key is the position in tfsList, value in the
   * index vector boolean indexResult = result.get(pair.getValue()); boolean
   * unifierResult = // getSubsumes(pair.getKey(), j);
   * (tfsList.get(pair.getValue()).subsumesBi(tfsList.get(j)) &
   * TFS.THIS_MORE_GENERAL) != 0; if (indexResult != unifierResult) {
   * logger.error("Wrong results for " + pair.getValue() + " vs. " + j + " i: "
   * + indexResult + " u: " + unifierResult); failure++; } else { success++; } }
   * } logger.info("test finished; successful: " + success + " failures: " +
   * failure); }
   */

  class RestrictFSConsumer implements EdgeConsumer {
    private int total;
    private Writer _out;

    public RestrictFSConsumer(Writer out) {
      _out = out;
      total = 0;
    }

    @Override
    public void addEdge(int id, int start, int end, String ruleName,
        List<?> subEdges, TFS fs) {
      ++total;
      if (interval != 0 && ((total % interval) == 0))
        logger.info(" FS  " + total);
      fs.restrict();
      try {
        _out.append(fs.toString());
        _out.append("\n");
      } catch (IOException e) {
        e.printStackTrace();
        System.exit(1);
      }
    }

    @Override
    public void setChartSize(int size) {
    }

    @Override
    public int added() {
      return total;
    }
  }

  /* read maxFS restricted FS from the given file */
  private List<TFS> getRestrictedFS(String restrFileName) {
    SimpleTfsConsumer cons = new SimpleTfsConsumer(maxFS);
    FSGrammar.readTFSFile(restrFileName, cons);
    List<TFS> result = cons.getTfsList();
    logger.info(result.size() + " restricted FSs read");
    return result;
  }


  public static Object loadFromFile(String filename)
  throws FileNotFoundException, IOException {
    try {
      ObjectInputStream ois =
        new ObjectInputStream(new FileInputStream(filename));
      Object fsi = ois.readObject();
      ois.close();
      return fsi;
    } catch (ClassNotFoundException e) {
      e.printStackTrace();
    }
    return null;
  }


  @SuppressWarnings("unused")
  private void
  doReadTFS(String TFSFilename, boolean justAdd) {
    // moderate restriction of feature structures to do an impressionistic
    // test of how many structures can be put into the index
    for (String feat : featuresToDelete) {
      gram.addFeatureToDelete(feat);
    }

    TfsConsumer cons = new TfsConsumer() {
      int total = 0;
      public boolean atEnd() { return (maxFS > 0 && total >= maxFS) ; }
      public void consume(TFS fs) { ++total; }
      public int added() { return total; }
    };
    FSGrammar.readTFSFile(TFSFilename, cons);
    logger.info("Finished reading of " + cons.added() + " structures, ");
  }


  void
  doReduceUnsolvedError(String indexDataName, List<TFS> fsList) {
    // reduce a specific error: DualUnifErrorProducer is used when the results
    // with and without intermediate copying differ. It takes a rule and two
    // argument feature structures as input

    SimpleTfsConsumer cons = new SimpleTfsConsumer(interval);
    FSGrammar.readTFSFile(indexDataName, cons);
    List<TFS> index = cons.getTfsList();
    @SuppressWarnings("unused")
    TFS[] rargstfs = index.toArray(new TFS[index.size()]);

    // TFSErrorProducer ep = new TFSErrorProducer();

    //logger.info(ep.reduce());
  }


  /**
   * @param args
   */
  public static void main(String[] args) {
    // Set up logging
    BasicConfigurator.configure();

    OptionParser parser = new OptionParser("t:m:s:i:as");
    OptionSet options = null;
    try {
      options = parser.parse(args);
    }
    catch (OptionException ex) {
      System.out.println("Error parsing options: " + ex);
      System.out.println(
          "Usage: crowl [-t(esttype) num] [-m maxFS] [-s(ave) outfile]\n" +
          "             [-i(nterval) num] [-a(dd)]");
      System.exit(1);
    }

    List<String> files = options.nonOptionArguments();
    if (files.size() < 2)
      return;
    int testtype = 1;
    int maxFS = 25000;
    int interval = 5000;
    int sFlag = 0;
    if (options.has("t")) {
      testtype = Integer.valueOf((String) options.valueOf("t"));
    }
    if (options.has("m")) {
      maxFS = Integer.valueOf((String) options.valueOf("m"));
    }
    if (options.has("s")) {
      sFlag = Integer.valueOf((String) options.valueOf("s"));
    }
    if (options.has("i")) {
      interval = Integer.valueOf((String) options.valueOf("i"));
    }
    Iterator<String> tfsFiles = files.iterator();
    // read the grammar
    TFSRunner tfm = new TFSRunner(tfsFiles.next(), maxFS, interval, sFlag);

    switch (testtype) {
    case 98: {
      // try to reduce feature structures that give erroneous results
      // read maxFS structures into memory and test it against different
      // versions of the index
      List<TFS> fsList = tfm.getRestrictedFS(tfsFiles.next());

      tfm.doReduceUnsolvedError(tfsFiles.next(), fsList);
      break;
    }
    case 99: {
      for (String feat : featuresToDelete) {
        tfm.gram.addFeatureToDelete(feat);
      }
      try {
        // open output file where all the restricted structures are written to
        String tfsfile = tfsFiles.next();
        FileWriter out = new FileWriter(tfsfile);
        tfm.gram.readTFSFiles(tfsFiles, tfm.new RestrictFSConsumer(out), 0);
        out.close();
        /*
         * // re-read the fs's from the given chart files and make sure all the
         * fs // from the newly written file are in that index tfsFiles =
         * files.iterator(); tfsFiles.next(); // grammar FileReader in = new
         * FileReader(tfsFiles.next()); // resfsfile FSIndex fsi = new
         * FSIndex(); AddToIndex aot = tfm.new AddToIndex(fsi, true);
         * tfm.readTFSFiles(tfsFiles, aot, maxFS); JxchgTokenizer jxchg = new
         * JxchgTokenizer(in); int i = 0 ; try { while (! jxchg.atEOF()) { ++i;
         * if (! fsi.contains(TFS.buildFS(jxchg, tfm.gram))) {
         * logger.error("FS in line " + i + " not in index"); } } } catch
         * (InvalidSyntaxException e) { e.printStackTrace(); } in.close();
         */
      } catch (IOException ioex) {
        ioex.printStackTrace();
      }
      break;
    }
    }
  }
}
