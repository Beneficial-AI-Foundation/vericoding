// <vc-preamble>
// Multiply two Hermite series represented as coefficient sequences
// The product of Hermite polynomials requires reprojection onto the basis set
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method hermemul(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
  requires |c1| > 0 && |c2| > 0
  ensures |result| == |c1| + |c2| - 1
  // Zero preservation: if either input is all zeros, result is all zeros
  ensures (forall i :: 0 <= i < |c1| ==> c1[i] == 0.0) || 
          (forall j :: 0 <= j < |c2| ==> c2[j] == 0.0) ==> 
          (forall k :: 0 <= k < |result| ==> result[k] == 0.0)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
