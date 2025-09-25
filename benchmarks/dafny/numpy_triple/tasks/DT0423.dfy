// <vc-preamble>
// Helper function to compute maximum of two integers
function Max(a: int, b: int): int
{
    if a >= b then a else b
}

/**
 * Subtract one Hermite series from another.
 * Returns the difference of two Hermite series c1 - c2.
 * The sequences of coefficients are from lowest order term to highest.
 * Shorter arrays are implicitly padded with zeros for subtraction.
 */
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method hermesub(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
    // The result length equals the maximum of input lengths
    ensures |result| == Max(|c1|, |c2|)
    // Each coefficient is the component-wise difference, with implicit zero padding
    ensures forall i :: 0 <= i < |result| ==>
        result[i] == (if i < |c1| then c1[i] else 0.0) - (if i < |c2| then c2[i] else 0.0)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
