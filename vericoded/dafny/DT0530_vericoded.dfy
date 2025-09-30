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
/* helper modified by LLM (iteration 2): Fixed type error by ensuring j is nat */
function GenerateRow(x_val: real, deg: nat): seq<real>
    ensures |GenerateRow(x_val, deg)| == deg + 1
    ensures forall j :: 0 <= j < |GenerateRow(x_val, deg)| ==> GenerateRow(x_val, deg)[j] == Pow(x_val, j)
    ensures GenerateRow(x_val, deg)[0] == 1.0
    ensures deg > 0 ==> GenerateRow(x_val, deg)[1] == x_val
{
    seq(deg + 1, (j: nat) => Pow(x_val, j))
}
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
  /* code modified by LLM (iteration 2): Using GenerateRow helper function */
  V := seq(|x|, i requires 0 <= i < |x| => GenerateRow(x[i], deg));
}
// </vc-code>
