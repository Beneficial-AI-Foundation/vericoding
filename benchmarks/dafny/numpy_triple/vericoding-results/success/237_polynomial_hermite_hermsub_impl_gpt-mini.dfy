// <vc-preamble>
/*
 * Dafny specification for Hermite polynomial series subtraction.
 * This file implements the specification for subtracting one Hermite series from another,
 * performing component-wise subtraction with missing coefficients treated as zero.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): MaxInt returns the maximum of two ints */
function MaxInt(a: int, b: int): int { if a >= b then a else b }
// </vc-helpers>

// <vc-spec>
method HermiteSub(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
    ensures |result| == if |c1| >= |c2| then |c1| else |c2|
    ensures forall i :: 0 <= i < |result| ==>
        if i < |c1| && i < |c2| then
            result[i] == c1[i] - c2[i]
        else if i < |c1| && i >= |c2| then
            result[i] == c1[i]
        else if i >= |c1| && i < |c2| then
            result[i] == -c2[i]
        else
            false  // This case should never occur given the length constraint
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): component-wise subtraction with missing coefficients treated as zero */
  var n := MaxInt(|c1|, |c2|);
  var a := new real[n];
  var i := 0;
  while i < n
    decreases n - i
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> (
      if j < |c1| && j < |c2| then a[j] == c1[j] - c2[j]
      else if j < |c1| && j >= |c2| then a[j] == c1[j]
      else if j >= |c1| && j < |c2| then a[j] == -c2[j]
      else false)
  {
    if i < |c1| && i < |c2| {
      a[i] := c1[i] - c2[i];
    } else if i < |c1| {
      a[i] := c1[i];
    } else {
      a[i] := -c2[i];
    }
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
