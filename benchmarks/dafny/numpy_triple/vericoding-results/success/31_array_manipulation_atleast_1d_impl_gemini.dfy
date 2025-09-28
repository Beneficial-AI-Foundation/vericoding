// <vc-preamble>
// For vectors that already have at least one dimension, atleast_1d is identity
// </vc-preamble>

// <vc-helpers>

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
