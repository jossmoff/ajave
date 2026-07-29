import org.sosy_lab.sv_benchmarks.Verifier;

// Like ArithmeticException1: i > 0 so division never throws.
// The catch block (with assert false) is unreachable.
// Expected: TRUE
public class Main {
  public static void main(String[] args) {
    try {
      int i = Verifier.nondetInt();
      Verifier.assume(i > 0);
      int k = 10 / i;
    } catch (ArithmeticException exc) {
      assert false;
    }
  }
}
