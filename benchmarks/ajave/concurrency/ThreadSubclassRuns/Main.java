// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: `class W extends Thread`
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   The worker sets n=1 and is joined before the read, so n is 1.
//
//   The shape is the point. Subclassing Thread is idiomatic Java, and the
//   implicit super() in W.<init> has `this` as its receiver -- an object
//   allocated in the *caller*, not in the constructor. A discovery pass that
//   traces Thread construction to an allocation inside the method it is
//   looking at cannot resolve it, so this was refused outright.
public class Main {
  static int n = 0;
  static class W extends Thread {
    public void run() { n = 1; }
  }
  public static void main(String[] args) throws Exception {
    W t = new W();
    t.start();
    t.join();
    assert n == 1;
  }
}
