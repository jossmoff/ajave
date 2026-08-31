// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: read-to-write lock upgrade
// Expected: no-deadlock=false
//
// Ground truth (by construction, NOT by observation):
//   ReentrantReadWriteLock does not support upgrading. Acquiring the write
//   lock requires that no reader holds the lock, and this thread is itself a
//   reader, so it waits for a read lock only it can release. The Javadoc says
//   so explicitly: "the read lock cannot be upgraded to the write lock".
//   One thread deadlocks against itself, needing no interleaving at all.
import java.util.concurrent.locks.ReentrantReadWriteLock;
public class Main {
  static final ReentrantReadWriteLock rw = new ReentrantReadWriteLock();
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Runnable() { public void run() { int q = 1; } });
    t.start();
    rw.readLock().lock();
    rw.writeLock().lock();   // cannot be granted: this thread holds a read lock
    rw.writeLock().unlock();
    rw.readLock().unlock();
  }
}
