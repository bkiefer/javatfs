package de.dfki.lt.loot.tfsdebugging;

//import de.dfki.lt.loot.gui.MainFrame;
import de.dfki.lt.loot.tfs.DagNode;
import de.dfki.lt.loot.tfs.TFS;

public class DualUnifErrorProducer extends AbstractTFSErrorProducer {

  public enum TestType { WRONG_FAILURE, WRONG_TMP_UNIF } ;

  private TestType ttype;

  private TFS replayRuleWithCopy(TFS[] currRargs) {
    TFS res = currRargs[0];
    for(int i = 0; i < currRargs.length - 1; ++i) {
      res = res.unifyFS(currRargs[i + 1], i);
      if (res == null)
        return null;
    }
    return res;
  }

  private TFS replayRuleTempFS(TFS[] currRargs) {
    TFS res = currRargs[0];
    for(int i = 0; i <= currRargs.length - 1; ++i) {
      if (! res.unifyOnly(currRargs[i + 1], i))
        return null;
    }
    return res.copyResult();
  }

  public DualUnifErrorProducer(TFS[] ruleAndArgs, TestType testType) {
    super(ruleAndArgs, ruleAndArgs.length);
    ttype = testType;
  }

  public boolean errorPersists() {
    TFS[] currRargs = getRestricted();

    TFS result0 = replayRuleWithCopy(currRargs);
    switch (ttype) {
    case WRONG_FAILURE: return result0 == null;
    case WRONG_TMP_UNIF: {
      TFS result1 = replayRuleTempFS(currRargs);
      if (result0 == null || result1 == null) return false;
      int result = result0.subsumesBi(result1);
      return (result != (DagNode.ARG_MORE_GENERAL | DagNode.THIS_MORE_GENERAL));
      }
    }
    return false;
  }

  @Override
  public String reduce() {
    reduceAll();

    String nl = System.getProperty("line.separator");
    StringBuilder sb = new StringBuilder();
    TFS[] currRargs = getRestricted();

    for (int i = 0 ; i < tfs.length ; ++i) {
      sb.append(currRargs[i].toString());
      sb.append(nl);
      //new MainFrame("rarg" + i, currRargs[i].dag());
      System.out.println("rarg" + i + "\n" + currRargs[i].dag());
    }
    switch (ttype) {
    case WRONG_FAILURE: break;
    case WRONG_TMP_UNIF: {
      TFS result0 = replayRuleWithCopy(currRargs);
      DagNode.recordFailures(true);
      TFS result1 = replayRuleTempFS(currRargs);
      result0.subsumesBi(result1); // mark failures
      DagNode.recordFailures(false);
      //new MainFrame("res0", result0.dag());
      //new MainFrame("res1", result1.dag());
      System.out.println("res0:\n" + result0.dag());
      System.out.println("res1:\n" + result1.dag());
      }
    }
    return sb.toString();
  }
}
