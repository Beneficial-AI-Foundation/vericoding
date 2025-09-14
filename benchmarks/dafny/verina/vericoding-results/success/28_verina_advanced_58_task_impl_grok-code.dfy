// <vc-preamble>
predicate NthUglyNumberPrecond(n: nat)
{
    n > 0
}
// </vc-preamble>

// <vc-helpers>
function Min(a: int, b: int): int
      { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method NthUglyNumber(n: int) returns (result: int)
    requires n > 0
    ensures result > 0
// </vc-spec>
// <vc-code>
{
  var ugly: seq<int> := [1];
  var p2 := 0;
  var p3 := 0;
  var p5 := 0;
  while |ugly| < n 
    invariant |ugly| >= 1
    invariant 0 <= p2 <= |ugly| - 1
    invariant 0 <= p3 <= |ugly| - 1
    invariant 0 <= p5 <= |ugly| - 1
    invariant forall i :: 0 <= i < |ugly| ==> ugly[i] >= 1
  {
    var n2 := ugly[p2] * 2;
    var n3 := ugly[p3] * 3;
    var n5 := ugly[p5] * 5;
    var next := Min(n2, Min(n3, n5));
    ugly := ugly + [next];
    if next == n2 { p2 := p2 + 1; }
    if next == n3 { p3 := p3 + 1; }
    if next == n5 { p5 := p5 + 1; }
  }
  result := ugly[n-1];
}
// </vc-code>
