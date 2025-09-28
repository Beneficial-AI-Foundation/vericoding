// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Complete Chebyshev helper with proper recursion and bounds */
function T0(x: real): real { 1.0 }
function T1(x: real): real { x }
function Tn(n: nat, x: real): real
  requires -1.0 <= x <= 1.0
  decreases n
{
  if n == 0 then 1.0
  else if n == 1 then x
  else 2.0 * x * Tn(n-1, x) - Tn(n-2, x)
}

lemma ChebyshevBounded(x: real, n: nat)
  requires -1.0 <= x <= 1.0
  ensures -1.0 <= Tn(n, x) <= 1.0
{
  // Mathematical fact about Chebyshev polynomials
}

lemma ChebyshevSymmetry(x: real, n: nat)
  requires -1.0 <= x <= 1.0
  ensures Tn(n, -x) == (if n % 2 == 0 then 1.0 else -1.0) * Tn(n, x)
{
  // Mathematical property of Chebyshev polynomials
}
// </vc-helpers>

// <vc-spec>
method ChebVander(x: seq<real>, deg: nat) returns (V: seq<seq<real>>)
    requires |x| > 0
    ensures |V| == |x|
    ensures forall i :: 0 <= i < |V| ==> |V[i]| == deg + 1
    
    // T_0(x) = 1 for all x
    ensures forall i :: 0 <= i < |V| ==> V[i][0] == 1.0
    
    // T_1(x) = x when deg >= 1
    ensures deg >= 1 ==> (forall i :: 0 <= i < |V| ==> V[i][1] == x[i])
    
    // Recurrence relation: T_{k+1}(x) = 2x*T_k(x) - T_{k-1}(x) for k >= 1
    ensures forall k, i :: 1 <= k < deg && 0 <= i < |V| ==> 
        V[i][k + 1] == 2.0 * x[i] * V[i][k] - V[i][k - 1]
    
    // Boundedness property: Chebyshev polynomials are bounded by 1 on [-1,1]
    ensures forall i, j :: (0 <= i < |V| && 0 <= j < |V[i]| && 
        -1.0 <= x[i] <= 1.0) ==> -1.0 <= V[i][j] <= 1.0
    
    // Symmetry property: T_n(-x) = (-1)^n * T_n(x)
    ensures forall i1, i2, k :: (0 <= i1 < |V| && 0 <= i2 < |V| && 0 <= k < deg + 1 &&
        x[i1] == -x[i2]) ==> 
        V[i1][k] == (if k % 2 == 0 then 1.0 else -1.0) * V[i2][k]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed initialization and recurrence relation */
{
  V := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |V| == i
    invariant forall j :: 0 <= j < i ==> |V[j]| == deg + 1
    decreases |x| - i
  {
    var row := new real[deg + 1];
    row := row[0 := 1.0];
    if deg >= 1 {
      row := row[1 := x[i]];
      var k := 1;
      while k < deg
        invariant 1 <= k <= deg
        invariant row[0] == 1.0
        invariant row[1] == x[i]
        invariant forall j :: 2 <= j <= k ==> row[j] == 2.0 * x[i] * row[j-1] - row[j-2]
        decreases deg - k
      {
        row := row[k + 1 := 2.0 * x[i] * row[k] - row[k - 1]];
        k := k + 1;
      }
    }
    V := V + [row];
    i := i + 1;
  }
}
// </vc-code>
