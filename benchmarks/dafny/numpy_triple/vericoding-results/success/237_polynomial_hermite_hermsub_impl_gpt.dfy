// <vc-preamble>
/*
 * Dafny specification for Hermite polynomial series subtraction.
 * This file implements the specification for subtracting one Hermite series from another,
 * performing component-wise subtraction with missing coefficients treated as zero.
 */
// </vc-preamble>

// <vc-helpers>
lemma lemma_LtMaxAndGeAImpliesLtB(i: int, a: int, b: int)
    requires 0 <= i
    requires 0 <= a && 0 <= b
    requires i < (if a >= b then a else b)
    requires i >= a
    ensures i < b
{
    if a >= b {
        assert i < a;
        assert false;
    } else {
        assert i < b;
    }
}
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
  var n := if |c1| >= |c2| then |c1| else |c2|;
  var r: seq<real> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==>
      if j < |c1| && j < |c2| then r[j] == c1[j] - c2[j]
      else if j < |c1| && j >= |c2| then r[j] == c1[j]
      else if j >= |c1| && j < |c2| then r[j] == -c2[j]
      else false
    decreases n - i
  {
    var v: real;
    if i < |c1| {
      if i < |c2| {
        v := c1[i] - c2[i];
      } else {
        v := c1[i];
      }
    } else {
      lemma_LtMaxAndGeAImpliesLtB(i, |c1|, |c2|);
      v := -c2[i];
    }
    r := r + [v];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
