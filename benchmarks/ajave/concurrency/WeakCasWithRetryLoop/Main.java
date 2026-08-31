// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: the retry loop weak CAS requires
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   The same update, retried until it succeeds. Nothing else touches `v`, so
//   the expected value stays 0 and the loop terminates as soon as one attempt
//   is not a spurious failure. The counter is then 1.
//
//   The companion to WeakCasNeedsRetryLoop: an engine that models spurious
//   failure must report this TRUE and its partner FALSE.
import java.util.concurrent.atomic.AtomicInteger;
public class Main {
  static final AtomicInteger v = new AtomicInteger(0);
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Runnable() { public void run() { int q = 1; } });
    t.start();
    while (!v.weakCompareAndSet(0, 1)) { }
    t.join();
    assert v.get() == 1;
  }
}
