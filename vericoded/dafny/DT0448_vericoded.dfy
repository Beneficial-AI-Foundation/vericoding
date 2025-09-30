// <vc-preamble>
/*
 * Dafny specification for Hermite polynomial series subtraction.
 * This file implements the specification for subtracting one Hermite series from another,
 * performing component-wise subtraction with missing coefficients treated as zero.
 */
// </vc-preamble>

// <vc-helpers>

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
  var maxLen := if |c1| >= |c2| then |c1| else |c2|;
  result := [];
  var i := 0;
  while i < maxLen
    invariant 0 <= i <= maxLen
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==>
      if j < |c1| && j < |c2| then
        result[j] == c1[j] - c2[j]
      else if j < |c1| && j >= |c2| then
        result[j] == c1[j]
      else if j >= |c1| && j < |c2| then
        result[j] == -c2[j]
      else
        false
  {
    if i < |c1| && i < |c2| {
      result := result + [c1[i] - c2[i]];
    } else if i < |c1| && i >= |c2| {
      result := result + [c1[i]];
    } else if i >= |c1| && i < |c2| {
      result := result + [-c2[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
