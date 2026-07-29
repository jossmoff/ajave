import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  public static void main(String[] args) {
    int x = Verifier.nondetInt();
    Verifier.assume(x >= 4);
    assert x > 3;
  }
}
