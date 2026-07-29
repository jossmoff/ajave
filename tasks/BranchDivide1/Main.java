import org.sosy_lab.sv_benchmarks.Verifier;

// Branch guards the division: only divides when x != 0.
// No exception can be thrown; assert is never reached.
// Expected: TRUE
public class Main {
  public static void main(String[] args) {
    int x = Verifier.nondetInt();
    int y = 0;
    if (x != 0) {
      y = 100 / x;
    }
    assert y != 99999;
  }
}
