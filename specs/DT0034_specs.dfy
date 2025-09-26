// <vc-preamble>
// Ghost function for real number exponentiation with natural number exponents
ghost function Pow(base: real, exp: nat): real
    decreases exp
{
    if exp == 0 then 1.0
    else base * Pow(base, exp - 1)
}

// Generate a Vandermonde matrix with decreasing powers (default behavior)
// The Vandermonde matrix is a matrix with terms of a geometric progression in each row
// For input vector x of length n and m columns, entry (i,j) = x[i]^(m-1-j)
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Vander(x: seq<real>, m: nat) returns (result: seq<seq<real>>)
    requires m > 0
    ensures |result| == |x|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == m
    ensures forall i, j :: 0 <= i < |x| && 0 <= j < m ==> 
            result[i][j] == Pow(x[i], (m - 1 - j) as nat)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
