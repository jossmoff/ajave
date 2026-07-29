import org.sosy_lab.sv_benchmarks.Verifier;

// Remainder by zero throws ArithmeticException just like division by zero.
// No handler: the uncaught exception is a runtime-exception-property violation.
// (The assert property checks assert reachability; the rem-by-zero manifests
// as a Check(DivByZero) obligation in roast's IR, same as for division.)
// Expected: FALSE
public class Main {
  public static void main(String[] args) {
    int x = Verifier.nondetInt();
    int y = x % 0;
    assert y == 0;
  }
}
