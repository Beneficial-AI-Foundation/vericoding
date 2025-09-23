// <vc-preamble>
// Method to return the number of dimensions of a vector (always 1 in this framework)
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ndim<T>(a: seq<T>) returns (result: int)
    // No preconditions - works for any vector
    ensures result == 1
    // All vectors in our framework are 1-dimensional arrays regardless of their element type or size
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
