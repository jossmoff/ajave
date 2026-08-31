// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ReentrantReadWriteLock read/write exclusion
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   The invariant is x == y, and the writer breaks it only while holding the
//   write lock. A read lock cannot be held while the write lock is, so the
//   reader never observes the intermediate state where x has been incremented
//   and y has not. Its two reads must agree.
//
//   This is the property a read/write lock exists to provide, and an engine
//   that modelled the read lock as exclusive would also report TRUE -- for the
//   wrong reason. ReadWriteLockConcurrentReaders is the companion that rules
//   that out.
import java.util.concurrent.locks.ReentrantReadWriteLock;
public class Main {
  static final ReentrantReadWriteLock rw = new ReentrantReadWriteLock();
  static int x = 0;
  static int y = 0;
  public static void main(String[] args) throws Exception {
    Thread writer = new Thread(new Runnable() {
      public void run() {
        rw.writeLock().lock();
        try { x++; y++; } finally { rw.writeLock().unlock(); }
      }
    });
    writer.start();
    rw.readLock().lock();
    int a, b;
    try { a = x; b = y; } finally { rw.readLock().unlock(); }
    writer.join();
    assert a == b;
  }
}
