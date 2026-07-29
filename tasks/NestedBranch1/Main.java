import org.sosy_lab.sv_benchmarks.Verifier;

// Nested if-else: every path sets result to the larger of x and y (or 1
// when both are non-positive). Inputs bounded to avoid overflow.
// Interval domain can close this: result in [1, 1000] on all paths.
// Expected: TRUE
public class Main {
  public static void main(String[] args) {
    int x = Verifier.nondetInt();
    int y = Verifier.nondetInt();
    Verifier.assume(x >= 1 && x <= 1000 && y >= 1 && y <= 1000);
    int result;
    if (x > y) {
      result = x;
    } else {
      result = y;
    }
    assert result >= 1;
  }
}
