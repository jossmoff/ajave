// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: latch-coordinated fan-out then aggregate
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   Two workers each write their own slot -- no shared write, so no race -- and
//   count the latch down. Main reads both slots only after await() returns,
//   which happens-after both countDowns, so it must see both writes. The sum
//   is exactly 3. This is the standard scatter/gather shape and it is the
//   combination that matters: per-thread slots for the writes, a latch for the
//   ordering.
import java.util.concurrent.CountDownLatch;
public class Main {
  static final CountDownLatch done = new CountDownLatch(2);
  static int slot0 = 0;
  static int slot1 = 0;
  public static void main(String[] args) throws Exception {
    Thread w0 = new Thread(new Runnable() {
      public void run() { slot0 = 1; done.countDown(); }
    });
    Thread w1 = new Thread(new Runnable() {
      public void run() { slot1 = 2; done.countDown(); }
    });
    w0.start(); w1.start();
    done.await();
    assert slot0 + slot1 == 3;
  }
}
