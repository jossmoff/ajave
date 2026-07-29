import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  public static void main(String[] args) {
    int x = Verifier.nondetInt();
    int y = 100 / x;
    assert y != 12345;
  }
}
