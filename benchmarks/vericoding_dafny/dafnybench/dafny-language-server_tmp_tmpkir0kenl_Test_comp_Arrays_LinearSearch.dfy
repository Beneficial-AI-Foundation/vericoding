// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method LinearSearch(a: array<int>, key: int) returns (n: nat)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || a[n] == key
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>

method PrintArray<A>(a: array?<A>) {
  if (a == null) {
    print "It's null\n";
  } else {
    var i := 0;
    while i < a.Length {
      print a[i], " ";
      i := i + 1;
    }
    print "\n";
  }
}


type lowercase = ch | 'a' <= ch <= 'z' witness 'd'



method DiagMatrix<A>(rows: int, cols: int, zero: A, one: A)
    returns (a: array2<A>)
    requires rows >= 0 && cols >= 0
{
  return new A[rows, cols]((x,y) => if x==y then one else zero);
}

method PrintMatrix<A>(m: array2<A>) {
  var i := 0;
  while i < m.Length0 {
    var j := 0;
    while j < m.Length1 {
      print m[i,j], " ";
      j := j + 1;
    }
    print "\n";
    i := i + 1;
  }
}