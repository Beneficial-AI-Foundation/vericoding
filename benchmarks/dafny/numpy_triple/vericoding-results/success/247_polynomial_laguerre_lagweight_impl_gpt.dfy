// <vc-preamble>
// Exponential function declaration for specification purposes
function Exp(x: real): real
{
  0.0  // Placeholder implementation for compilation
}

// Weight function method that computes exp(-x) for each element
// </vc-preamble>

// <vc-helpers>
function WeightSeq(x: seq<real>): seq<real>
  decreases |x|
  ensures |WeightSeq(x)| == |x|
  ensures forall i :: 0 <= i < |x| ==> WeightSeq(x)[i] == Exp(-x[i])
{
  if |x| == 0 then []
  else [Exp(-x[0])] + WeightSeq(x[1..])
}
// </vc-helpers>

// <vc-spec>
method lagweight(x: seq<real>) returns (w: seq<real>)
  // No special preconditions required for the weight function
  requires true
  // Result has same length as input
  ensures |w| == |x|
  // Each element of result is exp(-x[i]) for corresponding input element
  ensures forall i :: 0 <= i < |x| ==> w[i] == Exp(-x[i])
// </vc-spec>
// <vc-code>
{
  w := WeightSeq(x);
}
// </vc-code>
