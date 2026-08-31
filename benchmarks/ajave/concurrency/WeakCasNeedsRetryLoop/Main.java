// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: weakCompareAndSet may fail spuriously
// Expected: valid-assert=false
//
// Ground truth (by construction, from the specification, NOT by observation):
//   `weakCompareAndSet` is documented to "fail spuriously" -- it may return
//   false even when the witness value equals the expected one. That is the
//   whole reason it is cheaper than compareAndSet, and the reason its contract
//   says it must be used in a loop.
//
//   Here the result is used once, without a retry, so the update can simply
//   not happen and the counter stays 0. An engine that models weak CAS as an
//   exact compare-and-set reports this program safe.
import java.util.concurrent.atomic.AtomicInteger;
public class Main {
  static final AtomicInteger v = new AtomicInteger(0);
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Runnable() { public void run() { int q = 1; } });
    t.start();
    v.weakCompareAndSet(0, 1);   // no retry loop -- may spuriously do nothing
    t.join();
    assert v.get() == 1;
  }
}
