import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
  public static void main(String args[]) {
    try {
      int i = Verifier.nondetInt();
      //Verifier.assume(i - j == 1);
      Verifier.assume(i >= 4);
      int k = 10 / i ;
    } catch (ArithmeticException exc) {
      assert false;
    }
  }
}
