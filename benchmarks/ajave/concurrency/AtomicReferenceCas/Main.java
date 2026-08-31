// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: AtomicReference compareAndSet
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   Exactly one of the two compareAndSet calls can succeed: both propose to
//   replace the same initial value, and whichever lands second sees a
//   reference that no longer matches. So `winners` is exactly 1 under every
//   interleaving. A CAS modelled as anything other than a single atomic
//   read-compare-write would let both succeed.
import java.util.concurrent.atomic.AtomicReference;
public class Main {
  static final Object initial = new Object();
  static final Object a = new Object();
  static final Object b = new Object();
  static final AtomicReference<Object> ref = new AtomicReference<Object>(initial);
  static int winners = 0;
  static final Object counterLock = new Object();
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Runnable() {
      public void run() {
        if (ref.compareAndSet(initial, a)) {
          synchronized (counterLock) { winners++; }
        }
      }
    });
    t.start();
    if (ref.compareAndSet(initial, b)) {
      synchronized (counterLock) { winners++; }
    }
    t.join();
    assert winners == 1;
  }
}
