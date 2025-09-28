// <vc-preamble>
// Component-wise addition of two Hermite polynomial coefficient sequences
// Returns a sequence representing the sum of two Hermite series c1 + c2
// Coefficients are ordered from lowest to highest degree terms
// </vc-preamble>

// <vc-helpers>
function maxLen(c1: seq<real>, c2: seq<real>): nat
  ensures maxLen(c1, c2) == (if |c1| >= |c2| then |c1| else |c2|)
{
  if |c1| >= |c2| then |c1| else |c2|
}
// </vc-helpers>

// <vc-spec>
method hermeadd(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
  // The result length is the maximum of input lengths
  ensures |result| == if |c1| >= |c2| then |c1| else |c2|
  
  // Core coefficient addition property: each coefficient is sum of corresponding coefficients
  // Missing coefficients from shorter sequences are treated as zero
  ensures forall i :: 0 <= i < |result| ==>
    result[i] == (if i < |c1| then c1[i] else 0.0) + (if i < |c2| then c2[i] else 0.0)
// </vc-spec>
// <vc-code>
{
  var n := if |c1| >= |c2| then |c1| else |c2|;
  var a := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a.Length == n
    invariant forall k :: 0 <= k < i ==> a[k] == (if k < |c1| then c1[k] else 0.0) + (if k < |c2| then c2[k] else 0.0)
  {
    a[i] := (if i < |c1| then c1[i] else 0.0) + (if i < |c2| then c2[i] else 0.0);
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
