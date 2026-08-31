// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: the canonical two-account transfer deadlock
// Expected: no-deadlock=false
//
// Ground truth (by construction, NOT by observation):
//   transfer() locks the source account then the destination. Two transfers in
//   opposite directions therefore take the two locks in opposite orders, and
//   the interleaving where each grabs its first lock before either grabs its
//   second leaves both blocked. This is the textbook lock-order inversion, and
//   it is a real defect in real banking-style code -- the reason the ordered
//   variant next to this one exists.
public class Main {
  static class Account {
    int balance;
    Account(int b) { balance = b; }
  }
  static void transfer(Account from, Account to, int amount) {
    synchronized (from) {
      synchronized (to) {
        from.balance -= amount;
        to.balance += amount;
      }
    }
  }
  public static void main(String[] args) throws Exception {
    final Account a = new Account(100);
    final Account b = new Account(100);
    Thread t = new Thread(new Runnable() {
      public void run() { transfer(b, a, 10); }
    });
    t.start();
    transfer(a, b, 10);
    t.join();
  }
}
