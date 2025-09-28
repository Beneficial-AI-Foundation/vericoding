// <vc-preamble>
/*
 * Dafny specification for Hermite polynomial series subtraction.
 * This file implements the specification for subtracting one Hermite series from another,
 * performing component-wise subtraction with missing coefficients treated as zero.
 */
// </vc-preamble>

// <vc-helpers>

function max(a: int, b: int): int {
  if a >= b then a else b
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
  var len := max(|c1|, |c2|);
  result := [];
  var i := 0;
  while i < len
    invariant 0 <= i <= len
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
    var val: real;
    if i < |c1| && i < |c2| {
      val := c1[i] - c2[i];
    } else if i < |c1| && i >= |c2| {
      val := c1[i];
    } else if i >= |c1| && i < |c2| {
      val := -c2[i];
    } else {
      // This case should never be reached
      val := 0.0;
    }
    result := result + [val];
    i := i + 1;
  }
}
// </vc-code>
