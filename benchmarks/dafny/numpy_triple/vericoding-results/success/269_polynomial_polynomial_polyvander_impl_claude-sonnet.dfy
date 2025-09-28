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
  V := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |V| == i
    invariant forall k :: 0 <= k < i ==> |V[k]| == deg + 1
    invariant forall k, j :: 0 <= k < i && 0 <= j < |V[k]| ==> V[k][j] == Pow(x[k], j)
  {
    var row := [];
    var j := 0;
    while j <= deg
      invariant 0 <= j <= deg + 1
      invariant |row| == j
      invariant forall col :: 0 <= col < j ==> row[col] == Pow(x[i], col)
    {
      row := row + [Pow(x[i], j)];
      j := j + 1;
    }
    V := V + [row];
    i := i + 1;
  }
}
// </vc-code>
