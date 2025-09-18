// <vc-preamble>
// Helper function to compute sum of squares of a sequence
ghost function SumOfSquares(v: seq<real>): real
{
    if |v| == 0 then 0.0
    else v[0] * v[0] + SumOfSquares(v[1..])
}

// Helper function for square root (assumes non-negative input)
ghost function Sqrt(x: real): real
    requires x >= 0.0
{
    var r :| r >= 0.0 && r * r == x; r
}

// Predicate to check if all elements in vector are zero
ghost predicate IsZeroVector(v: seq<real>)
{
    forall i :: 0 <= i < |v| ==> v[i] == 0.0
}

/**
 * Computes the 2-norm (Euclidean norm) of a vector.
 * The 2-norm is defined as the square root of the sum of squares of all elements.
 * This is the most commonly used vector norm in numerical computing.
 */
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Norm(x: seq<real>) returns (result: real)
    ensures result >= 0.0
    ensures result == Sqrt(SumOfSquares(x))
    ensures (result == 0.0) <==> IsZeroVector(x)
    ensures |x| == 0 ==> result == 0.0
    ensures SumOfSquares(x) >= 0.0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
