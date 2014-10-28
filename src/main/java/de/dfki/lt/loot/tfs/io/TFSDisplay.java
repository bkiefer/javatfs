package de.dfki.lt.loot.tfs.io;

import java.io.IOException;
import java.util.concurrent.Semaphore;

import de.dfki.lt.loot.gui.DrawingPanel;
import de.dfki.lt.loot.gui.MainFrame;
import de.dfki.lt.loot.gui.layouts.CompactLayout;
import de.dfki.lt.loot.tfs.DagNode;
import de.dfki.lt.loot.tfs.TFS;
import de.dfki.lt.loot.tfsviz.DagModelAdapter;

class SysinWaiter implements Runnable {
  Semaphore _toRelease;

  SysinWaiter(Semaphore sem) { _toRelease = sem; }

  @Override
  public void run() {
    try { System.in.read(); }
    catch (IOException e) { }
    finally { _toRelease.release(); }
  }
}

public class TFSDisplay {
  /**/
  public static void displayOne(String title, DagNode dag, Semaphore sema) {
    DrawingPanel dp =
        new DrawingPanel(dag, new CompactLayout(), new DagModelAdapter());
    MainFrame thismf = new MainFrame(title,dp);
    if (sema != null) thismf.releaseOnAllClosed(sema);
  }
  /**/

  /*
  private static void displayOneS(String title, TFS tfs, Semaphore sema) {
    System.out.println(title);
    System.out.println(tfs);
    if (sema != null) { new Thread(new SysinWaiter(sema)).run(); }
  }
  */

  public static void displayAndWait(boolean wait, String title1, TFS thisTFS,
      String title2, TFS argTFS, String title3, TFS resultTFS) {
    Semaphore here = (wait ? new Semaphore(1) : null);
    try {
      if (wait) here.acquire();  // acquire the only available permit
      displayOne(title1,thisTFS.dag(), here);
      if (argTFS != null) displayOne(title2, argTFS.dag(), null);
      if (resultTFS != null) displayOne(title3, resultTFS.dag(), null);
      if (wait) here.acquire();  // wait for all wins closed
    } catch (InterruptedException e) {
    }
  }
  
  public static void displayAndWait(TFS thisTFS) {
    displayAndWait(true, "this", thisTFS, null, null, null, null);
  }
  public static void displayAndWait(TFS thisTFS, TFS argTFS) {
    displayAndWait(true, "this", thisTFS, "arg", argTFS, null, null);
  }
  public static void displayAndWait(TFS thisTFS, TFS argTFS, TFS resTFS) {
    displayAndWait(true, "this", thisTFS, "arg", argTFS, "result", resTFS);
  }
  public static void display(TFS thisTFS) {
    displayAndWait(false, "this", thisTFS, null, null, null, null);
  }
  public static void display(TFS thisTFS, TFS argTFS) {
    displayAndWait(false, "this", thisTFS, "arg", argTFS, null, null);
  }
  public static void display(TFS thisTFS, TFS argTFS, TFS resTFS) {
    displayAndWait(false, "this", thisTFS, "arg", argTFS, "result", resTFS);
  }

  public static void display(String string, DagNode dag) {
    displayOne(string, dag, null);
  }
}
