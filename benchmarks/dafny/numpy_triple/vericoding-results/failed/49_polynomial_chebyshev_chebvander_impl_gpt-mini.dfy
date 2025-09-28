// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): ChebRow function that constructs Chebyshev row */
function ChebRow(x: real, deg: nat): seq<real>
  decreases deg
  ensures |result| == deg + 1
  ensures result[0] == 1.0
  ensures deg >= 1 ==> result[1] == x
  ensures forall k :: 1 <= k < deg ==> result[k + 1] == 2.0 * x * result[k] - result[k - 1]
{
  if deg == 0 then
    [1.0]
  else if deg == 1 then
    [1.0, x]
  else
    var prev := ChebRow(x, deg - 1);
    var t := 2.0 * x * prev[|prev| - 1] - prev[|prev| - 2];
    prev + [t]
}

/* helper modified by LLM (iteration 5): ChebRowSymmetry lemma proving symmetry property */
lemma ChebRowSymmetry(x: real, deg: nat)
  decreases deg
  ensures forall k :: 0 <= k < deg + 1 ==> ChebRow(-x, deg)[k] == (if k % 2 == 0 then 1.0 else -1.0) * ChebRow(x, deg)[k]
{
  if deg <= 1 {
    // base cases: deg == 0 and deg == 1 follow directly from definition of ChebRow
  } else {
    ChebRowSymmetry(x, deg - 1);
    var prevp := ChebRow(x, deg - 1);
    var prevn := ChebRow(-x, deg - 1);
    assert ChebRow(-x, deg)[deg] == 2.0 * (-x) * prevn[|prevn| - 1] - prevn[|prevn| - 2];
    assert ChebRow(x, deg)[deg] == 2.0 * x * prevp[|prevp| - 1] - prevp[|prevp| - 2];
    var s1 := (if (deg - 1) % 2 == 0 then 1.0 else -1.0);
    var s2 := (if (deg - 2) % 2 == 0 then 1.0 else -1.0);
    assert prevn[|prevn| - 1] == s1 * prevp[|prevp| - 1];
    assert prevn[|prevn| - 2] == s2 * prevp[|prevp| - 2];
    calc {
      ChebRow(-x, deg)[deg];
      == { }
      2.0 * (-x) * prevn[|prevn| - 1] - prevn[|prevn| - 2];
      == { }
      2.0 * (-x) * (s1 * prevp[|prevp| - 1]) - (s2 * prevp[|prevp| - 2]);
      == { }
      (if deg % 2 == 0 then 1.0 else -1.0) * (2.0 * x * prevp[|prevp| - 1] - prevp[|prevp| - 2]);
    }
  }
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
{
  /* code modified by LLM (iteration 5): build Vandermonde matrix using ChebRow and invoke symmetry lemma */
  var idx := 0;
  V := [];
  while idx < |x|
    decreases |x| - idx
  {
    var row := ChebRow(x[idx], deg);
    V := V + [row];
    ChebRowSymmetry(x[idx], deg);
    idx := idx + 1;
  }
}

// </vc-code>
