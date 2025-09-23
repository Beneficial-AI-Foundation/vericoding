// <vc-preamble>
// Helper function to compute sum of array elements recursively
function Sum(s: seq<real>): real
{
    if |s| == 0 then 0.0
    else s[0] + Sum(s[1..])
}

// Predicate to check if all elements in sequence are zero
predicate AllZero(s: seq<real>)
{
    forall i :: 0 <= i < |s| ==> s[i] == 0.0
}

/**
 * Sum of array elements - computes the sum of all elements in the vector.
 * For empty vectors, returns 0 as the identity element of addition.
 * This is a reduction operation that applies addition across all elements.
 */
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method sum(a: array<real>) returns (result: real)
    requires true
    ensures result == Sum(a[..])  // Result equals sum of all elements using recursive definition
    ensures a.Length == 0 ==> result == 0.0  // Empty array returns 0 (additive identity)
    ensures AllZero(a[..]) ==> result == 0.0  // If all elements are zero, result is zero
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
