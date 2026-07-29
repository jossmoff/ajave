import org.sosy_lab.sv_benchmarks.Verifier;

// Interval domain can prove: x in [1,100], y = x*2 in [2,200], assert y > 0.
// Expected: TRUE
public class Main {
  public static void main(String[] args) {
    int x = Verifier.nondetInt();
    Verifier.assume(x >= 1 && x <= 100);
    int y = x * 2;
    assert y > 0;
  }
}
