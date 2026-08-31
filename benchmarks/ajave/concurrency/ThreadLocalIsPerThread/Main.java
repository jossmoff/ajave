// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: ThreadLocal gives each thread its own cell
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   Each thread stores into the same ThreadLocal and reads it back. The
//   storage is per thread, so neither can observe the other's value and both
//   read what they wrote, whatever the interleaving.
//
//   Modelled as an ordinary shared field, the two writes race and each thread
//   could read the other's value -- so this is exactly the program that
//   distinguishes a real ThreadLocal from a shared cell.
public class Main {
  static final ThreadLocal<Object> tl = new ThreadLocal<Object>();
  static final Object A = new Object();
  static final Object B = new Object();
  static boolean workerSawItsOwn = false;
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Runnable() {
      public void run() {
        tl.set(A);
        workerSawItsOwn = (tl.get() == A);
      }
    });
    t.start();
    tl.set(B);
    Object mine = tl.get();
    t.join();
    assert mine == B && workerSawItsOwn;
  }
}
