// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ConcurrentHashMap.putIfAbsent atomicity
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   putIfAbsent is atomic: the test for absence and the insertion cannot be
//   separated. Both threads offer a value for the same key, exactly one finds
//   it absent and gets null back, and the other sees the winner's value. So
//   `winners` is exactly 1 under every interleaving.
//
//   Modelled as a get followed by a put, both threads could see the key absent
//   and both would win -- which is the bug ConcurrentHashMap exists to prevent.
import java.util.concurrent.ConcurrentHashMap;
public class Main {
  static final Object KEY = new Object();
  static final Object A = new Object();
  static final Object B = new Object();
  static final ConcurrentHashMap<Object, Object> map = new ConcurrentHashMap<Object, Object>();
  static final Object countLock = new Object();
  static int winners = 0;
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Runnable() {
      public void run() {
        if (map.putIfAbsent(KEY, A) == null) {
          synchronized (countLock) { winners++; }
        }
      }
    });
    t.start();
    if (map.putIfAbsent(KEY, B) == null) {
      synchronized (countLock) { winners++; }
    }
    t.join();
    assert winners == 1;
  }
}
