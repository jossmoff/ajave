// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: read locks are shared, not exclusive
// Expected: valid-assert=false
//
// Ground truth (by construction, NOT by observation):
//   Two threads hold the read lock at the same time -- that is what a read
//   lock is for -- so the unsynchronised `hits++` inside the read section is a
//   genuine race, and the interleaving where both read 0 leaves hits at 1.
//   The assertion demands 2, so the program is incorrect.
//
//   This is the companion to ReadWriteLockNoTornRead. An engine that modelled
//   the read lock as exclusive would serialise the two sections and report
//   TRUE, which is a wrong TRUE for a program that really does race. The pair
//   pins both halves of the semantics: exclusion against writers, sharing
//   among readers.
import java.util.concurrent.locks.ReentrantReadWriteLock;
public class Main {
  static final ReentrantReadWriteLock rw = new ReentrantReadWriteLock();
  static int hits = 0;
  static class Reader implements Runnable {
    public void run() {
      rw.readLock().lock();
      try { hits++; } finally { rw.readLock().unlock(); }
    }
  }
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Reader());
    t.start();
    new Reader().run();
    t.join();
    assert hits == 2;
  }
}
