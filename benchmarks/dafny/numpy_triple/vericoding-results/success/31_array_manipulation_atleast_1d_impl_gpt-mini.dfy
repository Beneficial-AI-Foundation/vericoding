// <vc-preamble>
// For vectors that already have at least one dimension, atleast_1d is identity
// </vc-preamble>

// <vc-helpers>
function atleast_1d(arr: seq<real>): seq<real> { arr }
// </vc-helpers>

// <vc-spec>
method AtLeast1D(arr: seq<real>) returns (result: seq<real>)
    ensures result == arr
// </vc-spec>
// <vc-code>
{
  result := arr;
}
// </vc-code>
