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
function Row(xi: real, deg: nat): seq<real>
    ensures |Row(xi, deg)| == deg + 1
    ensures forall j :: 0 <= j < |Row(xi,deg)| ==> Row(xi,deg)[j] == Pow(xi, j)
    decreases deg
{
    if deg == 0 then [1.0]
    else Row(xi, deg - 1) + [Pow(xi, deg)]
}

function BuildV(x: seq<real>, deg: nat): seq<seq<real>>
    ensures |BuildV(x,deg)| == |x|
    ensures forall i :: 0 <= i < |BuildV(x,deg)| ==> |BuildV(x,deg)[i]| == deg + 1
    ensures forall i, j :: 0 <= i < |BuildV(x,deg)| && 0 <= j < |BuildV(x,deg)[i]| ==> BuildV(x,deg)[i][j] == Pow(x[i], j)
    decreases |x|
{
    if |x| == 0 then []
    else BuildV(x[..|x|-1], deg) + [Row(x[|x|-1], deg)]
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
  V := BuildV(x, deg);
}
// </vc-code>
