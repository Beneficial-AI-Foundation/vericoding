// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
{
  /* code modified by LLM (iteration 2): Remove duplicate var V declaration and directly assign to out variable V */
  V := [];
  for i := 0 to |x|-1 {
    var row: seq<real> := [];
    if deg >= 0 {
      row := row + [1.0];
    }
    if deg >= 1 {
      row := row + [x[i]];
    }
    var prev_prev: real := 1.0;  // T_0
    var prev: real := x[i];       // T_1
    var k: nat := 2;
    while k <= deg {
      var curr: real := 2.0 * x[i] * prev - prev_prev;
      row := row + [curr];
      prev_prev := prev;
      prev := curr;
      k := k + 1;
    }
    V := V + [row];
  }
}
// </vc-code>
