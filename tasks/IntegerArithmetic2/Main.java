import org.sosy_lab.sv_benchmarks.Verifier;

// x and y both nondet; assume they are positive. Their sum can overflow
// or wrap, but the assertion only requires sum > 0 which can fail
// (e.g. x = MAX_VALUE, y = 1 wraps to MIN_VALUE).
// Concrete engine finds this with INT_CANDIDATES containing MAX_VALUE.
// Expected: FALSE
public class Main {
  public static void main(String[] args) {
    int x = Verifier.nondetInt();
    int y = Verifier.nondetInt();
    Verifier.assume(x > 0 && y > 0);
    int sum = x + y;
    assert sum > 0;
  }
}
