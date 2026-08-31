// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: unsafe publication through a non-volatile flag
// Expected: valid-assert=false
//
// Ground truth (by construction, from the JLS, NOT by observation):
//   The writer stores `data` and then `ready`; the reader checks `ready` and,
//   if set, reads `data`. Neither field is volatile and no lock is taken, so
//   the two threads are unordered by happens-before and the reader's view of
//   `data` is not constrained by the writer having stored it first.
//
//   The JMM therefore permits the reader to observe `ready == 1` together with
//   the *stale* `data == 0`, and the assertion fails. This is the canonical
//   unsafe-publication bug, and making `ready` volatile is the fix.
//
//   THIS PROGRAM IS CORRECT UNDER SEQUENTIAL CONSISTENCY. Under SC, seeing
//   ready == 1 implies the write to data already happened, so the assertion
//   holds. An engine that only considers sequentially consistent executions
//   cannot find this bug -- it can only decline to prove the program, which is
//   what the DRF-SC gate makes it do. Reporting FALSE here requires modelling
//   a read that observes something other than the most recent write.
public class Main {
  static int data = 0;
  static int ready = 0;          // deliberately not volatile
  public static void main(String[] args) throws Exception {
    Thread writer = new Thread(new Runnable() {
      public void run() { data = 42; ready = 1; }
    });
    writer.start();
    if (ready == 1) {
      assert data == 42;
    }
    writer.join();
  }
}
