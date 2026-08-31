// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: TryLockSucceedsWhenFree
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   Regression for a defect where a modelled call advanced its own program
//   counter, which made Stmt::Assign discard the returned value: tryLock()'s
//   boolean was lost. Nothing else ever touches this lock, so tryLock() on it
//   returns true unconditionally.
import java.util.concurrent.locks.ReentrantLock;
public class Main {
  public static void main(String[] args) throws Exception {
    final ReentrantLock l = new ReentrantLock();
    Thread t = new Thread(new Runnable() { public void run() { int x = 1; } });
    t.start();
    boolean got = l.tryLock();
    assert got;
    l.unlock();
  }
}
