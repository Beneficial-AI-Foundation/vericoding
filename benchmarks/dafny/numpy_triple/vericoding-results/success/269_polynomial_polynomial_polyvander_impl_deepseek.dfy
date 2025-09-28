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
function FillRow(base: real, deg: nat): (row': seq<real>)
    ensures |row'| == deg + 1
    ensures forall j :: 0 <= j < |row'| ==> row'[j] == Pow(base, j)
    decreases deg
{
    if deg == 0 then
        [1.0]
    else
        var prev_row := FillRow(base, deg - 1);
        prev_row + [Pow(base, deg)]
}

lemma VandermondeRowProperties(x_i: real, deg: nat, row: seq<real>)
    requires |row| == deg + 1
    requires forall j :: 0 <= j < |row| ==> row[j] == Pow(x_i, j)
    ensures row[0] == 1.0
    ensures deg > 0 ==> row[1] == x_i
{}
/* helper modified by LLM (iteration 4): Simplified FillRow to recursive construction */
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
    /* code modified by LLM (iteration 4): Using recursive FillRow helper */
    V := [];
    var i := 0;
    while i < |x|
        invariant 0 <= i <= |x|
        invariant |V| == i
        invariant forall k :: 0 <= k < i ==> |V[k]| == deg + 1
        invariant forall k, j :: 0 <= k < i && 0 <= j < deg + 1 ==> V[k][j] == Pow(x[k], j)
        invariant forall k :: 0 <= k < i ==> V[k][0] == 1.0
        invariant deg > 0 ==> forall k :: 0 <= k < i ==> V[k][1] == x[k]
    {
        var row := FillRow(x[i], deg);
        V := V + [row];
        i := i + 1;
    }
}
// </vc-code>
