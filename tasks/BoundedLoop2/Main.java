import org.sosy_lab.sv_benchmarks.Verifier;

// Nondet loop bound, but tightly constrained. The assertion fails because
// x can be 0, making the loop body never execute, so sum stays 0 != 1.
// Expected: FALSE
public class Main {
  public static void main(String[] args) {
    int n = Verifier.nondetInt();
    Verifier.assume(n >= 0 && n <= 3);
    int sum = 0;
    for (int i = 0; i < n; i++) {
      sum++;
    }
    assert sum >= 1;
  }
}
