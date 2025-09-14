// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method PrintArray<A>(a: array?<A>)
{
  assume{:axiom} false;
}


type lowercase = ch | 'a' <= ch <= 'z' witness 'd'



method DiagMatrix<A>(rows: int, cols: int, zero: A, one: A)
    returns (a: array2<A>)
    requires rows >= 0 && cols >= 0
{
  assume{:axiom} false;
}

method PrintMatrix<A>(m: array2<A>)
{
  assume{:axiom} false;
}

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method LinearSearch(a: array<int>, key: int) returns (n: nat)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || a[n] == key
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] != key
    decreases a.Length - i
  {
    if a[i] == key {
      n := i;
      return;
    }
    i := i + 1;
  }
  n := a.Length;
}
// </vc-code>

