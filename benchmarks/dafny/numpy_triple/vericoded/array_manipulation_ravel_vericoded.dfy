// <vc-preamble>
// Method representing numpy.ravel for 1D arrays (vectors)
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ravel(a: seq<real>) returns (result: seq<real>)
  requires true  // No preconditions for 1D ravel operation
  ensures result == a  // Result is identical to input vector for 1D case
// </vc-spec>
// <vc-code>
{
  result := a;
}
// </vc-code>
