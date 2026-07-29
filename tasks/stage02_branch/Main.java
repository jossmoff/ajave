import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  public static void main(String[] args) {
    int x = Verifier.nondetInt();
    int y;
    if (x > 10) {
      y = x;
    } else {
      y = 10;
    }
    assert y >= 10;
  }
}
