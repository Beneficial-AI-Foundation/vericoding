// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function T(k: nat, x: real): real
{
  if k == 0 then 1.0
  else if k == 1 then x
  else 2.0 * x * T(k - 1, x) - T(k - 2, x)
}

lemma ChebyshevProperties(k: nat, x: real)
    ensures T(k, -x) == (if k % 2 == 0 then 1.0 else -1.0) * T(k, x)
    ensures -1.0 <= x <= 1.0 ==> -1.0 <= T(k, x) <= 1.0
    decreases k
{
    if k > 1 {
        ChebyshevProperties(k - 1, x);
        ChebyshevProperties(k - 2, x);
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
  V := [];
  var i := 0;
  while i < |x|
    invariant |V| == i
    invariant forall j :: 0 <= j < i ==> |V[j]| == deg + 1
    invariant forall j, k :: (0 <= j < i && 0 <= k <= deg) ==> V[j][k] == T(k, x[j])
  {
    var row_arr := new real[deg + 1];
    if deg + 1 > 0 {
      row_arr[0] := 1.0;
    }
    if deg >= 1 {
      row_arr[1] := x[i];
    }
    var k := 1;
    while k < deg
      invariant 1 <= k <= deg
      invariant forall l :: 0 <= l <= k ==> row_arr[l] == T(l, x[i])
    {
      row_arr[k+1] := 2.0 * x[i] * row_arr[k] - row_arr[k-1];
      k := k + 1;
    }
    var row_seq := row_arr[..];
    V := V + [row_seq];
    i := i + 1;
  }

  forall i, j | 0 <= i < |V| && 0 <= j < |V[i]| && -1.0 <= x[i] <= 1.0
    ensures -1.0 <= V[i][j] <= 1.0
  {
    ChebyshevProperties(j, x[i]);
  }

  forall i1, i2, k | 0 <= i1 < |V| && 0 <= i2 < |V| && 0 <= k < deg + 1 && x[i1] == -x[i2]
    ensures V[i1][k] == (if k % 2 == 0 then 1.0 else -1.0) * V[i2][k]
  {
    ChebyshevProperties(k, x[i2]);
  }
}
// </vc-code>
