// <vc-preamble>
predicate NthUglyNumberPrecond(n: nat)
{
    n > 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added min function for integer comparison */
function min(a: int, b: int): int
{
  if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method NthUglyNumber(n: int) returns (result: int)
    requires n > 0
    ensures result > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Implemented nth ugly number using DP with three pointers, added bounds invariants */
{
  var ugly := [1];
  var i2 := 0;
  var i3 := 0;
  var i5 := 0;
  while |ugly| < n
    invariant |ugly| >= 1
    invariant 0 <= i2 < |ugly|
    invariant 0 <= i3 < |ugly|
    invariant 0 <= i5 < |ugly|
    invariant forall k :: 0 <= k < |ugly| ==> ugly[k] > 0
  {
    var next2 := ugly[i2] * 2;
    var next3 := ugly[i3] * 3;
    var next5 := ugly[i5] * 5;
    var next := min(next2, min(next3, next5));
    ugly := ugly + [next];
    if next == next2 { i2 := i2 + 1; }
    if next == next3 { i3 := i3 + 1; }
    if next5 == next { i5 := i5 + 1; }
  }
  result := ugly[n-1];
}
// </vc-code>
