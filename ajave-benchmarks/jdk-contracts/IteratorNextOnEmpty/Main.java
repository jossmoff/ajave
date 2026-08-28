// Part of ajave's own verification benchmark suite.
//
// SPDX-License-Identifier: Apache-2.0
//
// Feature under test: IteratorNextOnEmpty
// Expected: valid-assert=n/a, no-runtime-exception=false

public class Main {

  public static void main(String[] args) {
    java.util.Iterator<String> it = new java.util.ArrayList<String>().iterator();
    String s = it.next();
    assert s != null;
  }
}
