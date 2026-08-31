// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: the canonical loop guard around wait
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   Identical to SpuriousWakeupBreaksIfGuard except the guard is `while`. A
//   spurious return re-tests the condition and waits again, so the decrement
//   only ever runs with count > 0 and the assertion holds.
//
//   The pair isolates the guard as the cause: an engine that models spurious
//   wakeups must report this one TRUE and its partner FALSE. One that models
//   them not at all reports both TRUE, and one that always wakes spuriously
//   would deadlock this one.
public class Main {
  static final Object lock = new Object();
  static int count = 0;
  public static void main(String[] args) throws Exception {
    Thread producer = new Thread(new Runnable() {
      public void run() { synchronized (lock) { count++; lock.notifyAll(); } }
    });
    producer.start();
    synchronized (lock) {
      while (count == 0) {
        try { lock.wait(); } catch (InterruptedException e) { return; }
      }
      count--;
      assert count >= 0;
    }
    producer.join();
  }
}
