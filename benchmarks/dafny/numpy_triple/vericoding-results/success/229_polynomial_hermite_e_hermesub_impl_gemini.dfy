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
/**
 * Helper to get a coefficient from a sequence, returning 0.0 for out-of-bounds indices.
 */
function GetCoeff(c: seq<real>, i: int): real
{
    if 0 <= i < |c| then c[i] else 0.0
}
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
  var n := Max(|c1|, |c2|);
  result := seq(n, i => GetCoeff(c1, i) - GetCoeff(c2, i));
}
// </vc-code>
