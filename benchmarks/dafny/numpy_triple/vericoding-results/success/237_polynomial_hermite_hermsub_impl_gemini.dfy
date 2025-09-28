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
  var len1 := |c1|;
  var len2 := |c2|;
  var max_len := if len1 >= len2 then len1 else len2;
  result := [];
  var i: int := 0;

  while i < max_len
    invariant 0 <= i <= max_len
    invariant |result| == i
    invariant |c1| == len1 && |c2| == len2
    invariant forall j :: 0 <= j < i ==> 
        result[j] == (if j < len1 then c1[j] else 0.0) - (if j < len2 then c2[j] else 0.0)
  {
    var val1: real := if i < len1 then c1[i] else 0.0;
    var val2: real := if i < len2 then c2[i] else 0.0;
    result := result + [val1 - val2];
    i := i + 1;
  }
}
// </vc-code>
