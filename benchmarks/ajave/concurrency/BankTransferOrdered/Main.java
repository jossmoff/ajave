// Part of ajave's own concurrency benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: lock ordering as the fix for transfer deadlock
// Expected: no-deadlock=true
//
// Ground truth (by construction, NOT by observation):
//   Both threads acquire the two accounts in the same global order (by id),
//   regardless of transfer direction. A cycle in the wait-for graph needs two
//   threads holding locks in opposite orders, which a total order on
//   acquisition makes impossible. This is the same program as
//   BankTransferDeadlock with the standard fix applied, so the pair isolates
//   the ordering as the cause.
public class Main {
  static class Account {
    final int id;
    int balance;
    Account(int id, int b) { this.id = id; balance = b; }
  }
  static void transfer(Account from, Account to, int amount) {
    Account first  = from.id < to.id ? from : to;
    Account second = from.id < to.id ? to : from;
    synchronized (first) {
      synchronized (second) {
        from.balance -= amount;
        to.balance += amount;
      }
    }
  }
  public static void main(String[] args) throws Exception {
    final Account a = new Account(0, 100);
    final Account b = new Account(1, 100);
    Thread t = new Thread(new Runnable() {
      public void run() { transfer(b, a, 10); }
    });
    t.start();
    transfer(a, b, 10);
    t.join();
  }
}
