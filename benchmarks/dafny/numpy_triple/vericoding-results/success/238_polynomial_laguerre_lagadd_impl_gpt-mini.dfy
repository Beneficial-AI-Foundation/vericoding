// <vc-preamble>
// Add one Laguerre series to another
// Performs component-wise addition of two Laguerre series coefficients
// with zero padding for the shorter sequence
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a >= b then a else b }
// </vc-helpers>

// <vc-spec>
method lagadd(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
  // The result length is the maximum of the input lengths
  ensures |result| == (if |c1| >= |c2| then |c1| else |c2|)
  
  // Component-wise addition with zero padding
  ensures forall i :: 0 <= i < |result| ==>
    result[i] == (if i < |c1| then c1[i] else 0.0) + 
                 (if i < |c2| then c2[i] else 0.0)
  
  // Non-empty inputs produce non-empty output
  ensures (|c1| > 0 || |c2| > 0) ==> |result| > 0
// </vc-spec>
// <vc-code>
{
  var m := max(|c1|, |c2|);
  var a := new real[m];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant forall j :: 0 <= j < i ==> a[j] == (if j < |c1| then c1[j] else 0.0) + (if j < |c2| then c2[j] else 0.0)
  {
    a[i] := (if i < |c1| then c1[i] else 0.0) + (if i < |c2| then c2[i] else 0.0);
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
