import org.sosy_lab.sv_benchmarks.Verifier;

// Like ArithmeticException1 but without the assume: i can be 0,
// so the division throws, the catch is taken, and assert false fires.
// Expected: FALSE
public class Main {
  public static void main(String[] args) {
    try {
      int i = Verifier.nondetInt();
      int k = 10 / i;
    } catch (ArithmeticException exc) {
      assert false;
    }
  }
}
