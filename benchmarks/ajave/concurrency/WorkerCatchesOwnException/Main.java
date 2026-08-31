// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: exception-carrying control flow inside a worker thread
// Expected: valid-assert=true
//
// Ground truth (by construction, NOT by observation):
//   The worker throws and catches its own exception, setting `handled` on the
//   way out. main joins before reading it, so the write is visible and the
//   assertion holds under every interleaving.
//
//   An interpreter that treats a throw as "terminate the thread" -- which is
//   what ours did -- never runs the handler, so `handled` stays false and this
//   looks violated. The thread does not die here; it recovers.
public class Main {
  static boolean handled = false;
  public static void main(String[] args) throws Exception {
    Thread t = new Thread(new Runnable() {
      public void run() {
        try {
          throw new RuntimeException("boom");
        } catch (RuntimeException e) {
          handled = true;
        }
      }
    });
    t.start();
    t.join();
    assert handled;
  }
}
