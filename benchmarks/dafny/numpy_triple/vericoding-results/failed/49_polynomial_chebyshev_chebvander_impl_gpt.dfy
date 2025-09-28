// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): define (-1)^k as real */
function PowNegOne(k: nat): real
{
  if k % 2 == 0 then 1.0 else -1.0
}

/* helper modified by LLM (iteration 3): Chebyshev polynomial value via recurrence */
function ChebVal(k: nat, t: real): real
  decreases k
{
  if k == 0 then 1.0
  else if k == 1 then t
  else 2.0 * t * ChebVal(k - 1, t) - ChebVal(k - 2, t)
}

/* helper modified by LLM (iteration 3): parity step for (-1)^k */
lemma PowNegOneSucc(k: nat)
  ensures PowNegOne(k + 1) == -PowNegOne(k)
{
  if k % 2 == 0 {
    assert (k + 1) % 2 == 1;
    assert PowNegOne(k) == 1.0;
    assert PowNegOne(k + 1) == -1.0;
  } else {
    assert (k + 1) % 2 == 0;
    assert PowNegOne(k) == -1.0;
    assert PowNegOne(k + 1) == 1.0;
  }
}

/* helper modified by LLM (iteration 3): parity invariance for k and k-2 */
lemma PowNegOneMinusTwo(k: nat)
  requires k >= 2
  ensures PowNegOne(k - 2) == PowNegOne(k)
{
  if k % 2 == 0 {
    assert (k - 2) % 2 == 0;
    assert PowNegOne(k - 2) == 1.0;
    assert PowNegOne(k) == 1.0;
  } else {
    assert (k - 2) % 2 == 1;
    assert PowNegOne(k - 2) == -1.0;
    assert PowNegOne(k) == -1.0;
  }
}

/* helper modified by LLM (iteration 3): symmetry of Chebyshev polynomials */
lemma SymmetryCheb(t: real, k: nat)
  ensures ChebVal(k, -t) == PowNegOne(k) * ChebVal(k, t)
  decreases k
{
  if k == 0 {
  } else if k == 1 {
  } else {
    SymmetryCheb(t, (k - 1) as nat);
    SymmetryCheb(t, (k - 2) as nat);
    PowNegOneSucc((k - 1) as nat);
    PowNegOneMinusTwo(k);
    calc {
      ChebVal(k, -t);
      == { }
      2.0 * (-t) * ChebVal((k - 1) as nat, -t) - ChebVal((k - 2) as nat, -t);
      == { }
      -2.0 * t * (ChebVal((k - 1) as nat, -t)) - ChebVal((k - 2) as nat, -t);
      == { }
      -2.0 * t * (PowNegOne((k - 1) as nat) * ChebVal((k - 1) as nat, t)) - (PowNegOne((k - 2) as nat) * ChebVal((k - 2) as nat, t));
      == { }
      (-PowNegOne((k - 1) as nat)) * (2.0 * t * ChebVal((k - 1) as nat, t)) - PowNegOne((k - 2) as nat) * ChebVal((k - 2) as nat, t);
      == { PowNegOneSucc((k - 1) as nat); }
      PowNegOne(k) * (2.0 * t * ChebVal((k - 1) as nat, t)) - PowNegOne((k - 2) as nat) * ChebVal((k - 2) as nat, t);
      == { PowNegOneMinusTwo(k); }
      PowNegOne(k) * (2.0 * t * ChebVal((k - 1) as nat, t)) - PowNegOne(k) * ChebVal((k - 2) as nat, t);
      == { }
      PowNegOne(k) * (2.0 * t * ChebVal((k - 1) as nat, t) - ChebVal((k - 2) as nat, t));
      == { }
      PowNegOne(k) * ChebVal(k, t);
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
  /* code modified by LLM (iteration 3): build Vandermonde via arrays, populate with ChebVal, and invoke symmetry lemma */
  var n: int := |x|;
  var A := new seq<real>[n];
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n
    invariant A != null && A.Length == n
    invariant forall j :: 0 <= j < i ==> |A[j]| == deg + 1
    invariant forall j, k :: 0 <= j < i && 0 <= k < deg + 1 ==> A[j][k] == ChebVal(k as nat, x[j])
  {
    var m: int := deg + 1;
    var row := new real[m];
    var k: int := 0;
    while k < m
      invariant 0 <= k <= m
      invariant row != null && row.Length == m
      invariant forall t: int :: 0 <= t < k ==> row[t] == ChebVal(t as nat, x[i])
    {
      row[k] := ChebVal(k as nat, x[i]);
      k := k + 1;
    }
    A[i] := row[..];

    // Instantiate symmetry lemma for this row for all degrees
    k := 0;
    while k < m
      invariant 0 <= k <= m
    {
      SymmetryCheb(x[i], k as nat);
      k := k + 1;
    }

    i := i + 1;
  }
  V := A[..];
}
// </vc-code>
