// <vc-preamble>
// Method to multiply two Hermite series represented as coefficient sequences
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method hermmul(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
  ensures
    // Empty input handling: if either input is empty, return single zero coefficient
    (|c1| == 0 || |c2| == 0) ==> (|result| == 1 && result[0] == 0.0)
  ensures
    // Non-empty inputs have correct output size: m + n - 1 coefficients
    (|c1| > 0 && |c2| > 0) ==> |result| == |c1| + |c2| - 1
  ensures
    // Multiplication by constant polynomial (c2 has single coefficient)
    (|c2| == 1 && |c1| > 0) ==> 
      (|result| == |c1| && forall i :: 0 <= i < |c1| ==> result[i] == c1[i] * c2[0])
  ensures
    // Multiplication by constant polynomial (c1 has single coefficient)  
    (|c1| == 1 && |c2| > 0) ==> 
      (|result| == |c2| && forall i :: 0 <= i < |c2| ==> result[i] == c2[i] * c1[0])
  ensures
    // Zero polynomial property: if either input is all zeros, result is all zeros
    ((|c1| > 0 && forall i :: 0 <= i < |c1| ==> c1[i] == 0.0) ||
     (|c2| > 0 && forall j :: 0 <= j < |c2| ==> c2[j] == 0.0)) ==>
      (forall k :: 0 <= k < |result| ==> result[k] == 0.0)
  ensures
    // Result is never empty
    |result| >= 1
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
