import org.sosy_lab.sv_benchmarks.Verifier;

// Loop runs exactly 5 times accumulating a sum. The final value is
// deterministic: sum == 10. The assertion checks a weaker bound.
// Expected: TRUE
public class Main {
  public static void main(String[] args) {
    int sum = 0;
    for (int i = 0; i < 5; i++) {
      sum += 2;
    }
    assert sum == 10;
  }
}
