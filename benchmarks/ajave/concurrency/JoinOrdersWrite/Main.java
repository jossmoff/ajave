// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: JoinOrdersWrite
// Expected: valid-assert=true, no-runtime-exception=n/a
//
// Ground truth (by construction, NOT by observation):
//   join() establishes happens-before between the thread's final action and
//   the joiner's next action (JLS 17.4.5). The write in run() is therefore
//   visible and complete before the assert, under every schedule.

public class Main {

  static class Setter implements Runnable {
    int value = 0;
    public void run() { value = 42; }
  }
  public static void main(String[] args) throws Exception {
    Setter s = new Setter();
    Thread t = new Thread(s);
    t.start();
    try { t.join(); } catch (InterruptedException e) { }
    assert s.value == 42;
  }
}
