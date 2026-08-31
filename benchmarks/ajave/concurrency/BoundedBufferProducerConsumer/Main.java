// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: the classic wait/notify bounded buffer
// Expected: no-deadlock=true
//
// Ground truth (by construction, NOT by observation):
//   Producer and consumer both test their condition in a `while` loop and use
//   notifyAll, so no signal can be missed and no thread can wake to a
//   condition that has since changed. The buffer holds one item and exactly
//   one item is produced and consumed, so neither party can wait forever:
//   whenever one blocks, the other has work it can do.
//
//   This is the shape the wait/notify litmus tests abstract, written the way
//   it appears in real code -- guarded loop, notifyAll, shared monitor.
public class Main {
  static final Object lock = new Object();
  static int count = 0;
  static final int CAPACITY = 1;
  public static void main(String[] args) throws Exception {
    Thread producer = new Thread(new Runnable() {
      public void run() {
        synchronized (lock) {
          while (count == CAPACITY) {
            try { lock.wait(); } catch (InterruptedException e) { return; }
          }
          count++;
          lock.notifyAll();
        }
      }
    });
    producer.start();
    synchronized (lock) {
      while (count == 0) {
        try { lock.wait(); } catch (InterruptedException e) { return; }
      }
      count--;
      lock.notifyAll();
    }
    producer.join();
  }
}
