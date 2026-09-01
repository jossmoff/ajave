// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: a lambda that captures a local
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   The captured value is 7, so the worker stores 7 and the joined read sees it.
//
//   Capturing is the harder half: the captured values are operands of the
//   invokedynamic and become leading parameters of the synthesised
//   implementation method, so the object standing in for the lambda has to
//   carry them and pass them on.
public class Main {
  static int n = 0;
  public static void main(String[] args) throws Exception {
    int captured = 7;
    Thread t = new Thread(() -> { n = captured; });
    t.start();
    t.join();
    assert n == 7;
  }
}
