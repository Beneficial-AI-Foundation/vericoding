// <vc-preamble>
// Exponential function declaration for specification purposes
function Exp(x: real): real
{
  0.0  // Placeholder implementation for compilation
}

// Weight function method that computes exp(-x) for each element
// </vc-preamble>

// <vc-helpers>

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
  w := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |w| == i
    invariant forall j :: 0 <= j < i ==> w[j] == Exp(-x[j])
  {
    w := w + [Exp(-x[i])];
    i := i + 1;
  }
}
// </vc-code>
