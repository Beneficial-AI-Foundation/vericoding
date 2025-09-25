// <vc-preamble>
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Determinant(X: array2<int>, M: int) returns (z: int)
  requires 1 <= M;
  requires X != null && M == X.Length0 && M == X.Length1;
  modifies X;
// </vc-spec>
// <vc-code>
{
  var y := X[1-1,1-1];
  var a := 1;
  while (a != M)
    invariant 1 <= a <= M;
  {
    var b := a + 1;
    while (b != M+1)
      invariant a+1 <= b <= M+1;
    {
      var c := M;
      while (c != a)
        invariant a <= c <= M;
      {
        assume X[a-1,a-1] != 0;
        X[b-1, c-1] := X[b-1,c-1] - X[b-1,a-1] / X[a-1,a-1] * X[a-1,c-1];
        c := c - 1;
      }
      b := b + 1;
    }
    a := a + 1;
    y := y * X[a-1,a-1];
  }
  z := y;
}
// </vc-code>
