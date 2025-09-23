// <vc-preamble>
// Power function for real numbers with natural number exponents
function Pow(base: real, exp: nat): real
    decreases exp
{
    if exp == 0 then 1.0
    else base * Pow(base, exp - 1)
}

// Generate Vandermonde matrix of given degree for sample points x
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method PolyVander(x: seq<real>, deg: nat) returns (V: seq<seq<real>>)
    // Input constraints
    requires |x| >= 0
    
    // Output structure constraints
    ensures |V| == |x|  // Same number of rows as input points
    ensures forall i :: 0 <= i < |V| ==> |V[i]| == deg + 1  // Each row has deg+1 columns
    
    // Vandermonde matrix property: V[i,j] = x[i]^j
    ensures forall i, j :: 0 <= i < |V| && 0 <= j < |V[i]| ==> V[i][j] == Pow(x[i], j)
    
    // Specific properties from the Lean specification
    ensures forall i :: 0 <= i < |V| ==> V[i][0] == 1.0  // First column is all 1s
    ensures deg > 0 ==> forall i :: 0 <= i < |V| ==> V[i][1] == x[i]  // Second column equals input when deg > 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
