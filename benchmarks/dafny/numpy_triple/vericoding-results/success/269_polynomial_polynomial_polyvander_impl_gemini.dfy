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
/* helper modified by LLM (iteration 5): [recursive implementation with stronger ensures] */
function GenerateRow(xi: real, deg: nat): (r: seq<real>)
    decreases deg
    ensures |r| == deg + 1
    ensures forall j: nat :: j < |r| ==> r[j] == Pow(xi, j)
    ensures r[0] == 1.0
    ensures deg > 0 ==> r[1] == xi
{
    if deg == 0 then
        [Pow(xi, 0)]
    else
        GenerateRow(xi, deg - 1) + [Pow(xi, deg)]
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
  /* code modified by LLM (iteration 5): [use while loop to build sequence element by element] */
  V := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |V| == i
    invariant forall k :: 0 <= k < |V| ==> |V[k]| == deg + 1
    invariant forall k, j :: 0 <= k < |V| && 0 <= j < |V[k]| ==> V[k][j] == Pow(x[k], j)
    invariant forall k :: 0 <= k < |V| ==> V[k][0] == 1.0
    invariant deg > 0 ==> forall k :: 0 <= k < |V| ==> V[k][1] == x[k]
  {
    var row := GenerateRow(x[i], deg);
    V := V + [row];
    i := i + 1;
  }
}
// </vc-code>
