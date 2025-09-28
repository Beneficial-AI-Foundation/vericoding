// <vc-preamble>
// Ghost function to compute the i-th Hermite polynomial evaluated at point t
// Following the recurrence: H_0(t) = 1, H_1(t) = 2t, H_n(t) = 2t * H_{n-1}(t) - 2(n-1) * H_{n-2}(t)
ghost function HermitePolynomial(degree: nat, t: real): real
    decreases degree
{
    if degree == 0 then 1.0
    else if degree == 1 then 2.0 * t
    else 2.0 * t * HermitePolynomial(degree - 1, t) - 2.0 * (degree - 1) as real * HermitePolynomial(degree - 2, t)
}

// Method to create 2D Hermite Vandermonde matrix
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): executable Hermite evaluator as function */
function HermitePolynomial_exec(degree: nat, t: real): real
  decreases degree
{
  if degree == 0 then 1.0
  else if degree == 1 then 2.0 * t
  else 2.0 * t * HermitePolynomial_exec(degree - 1, t) - 2.0 * (degree - 1) as real * HermitePolynomial_exec(degree - 2, t)
}

/* helper modified by LLM (iteration 5): lemma relating executable and ghost HermitePolynomial */
lemma HermitePolynomial_match(degree: nat, t: real)
  ensures HermitePolynomial_exec(degree, t) == HermitePolynomial(degree, t)
  decreases degree
{
  if degree == 0 {
  } else if degree == 1 {
  } else {
    HermitePolynomial_match(degree - 1, t);
    HermitePolynomial_match(degree - 2, t);
  }
}

/* helper modified by LLM (iteration 5): div/mod decomposition properties for indexing */
lemma DivMod_decomposition(idx: nat, ydeg: nat)
  requires ydeg + 1 > 0
  ensures idx == (ydeg + 1) * (idx / (ydeg + 1)) + (idx % (ydeg + 1))
  ensures idx / (ydeg + 1) <= idx
  ensures idx % (ydeg + 1) < ydeg + 1
{
}

// </vc-helpers>

// <vc-spec>
method hermvander2d(x: seq<real>, y: seq<real>, xdeg: nat, ydeg: nat) returns (V: seq<seq<real>>)
    requires |x| == |y|
    requires xdeg >= 0 && ydeg >= 0
    ensures |V| == |x|
    // Each row has the correct size
    ensures forall k :: 0 <= k < |V| ==> |V[k]| == (xdeg + 1) * (ydeg + 1)
    // The first column (i=0, j=0) is all ones
    ensures forall k :: 0 <= k < |V| ==> 
        (xdeg + 1) * (ydeg + 1) > 0 ==> V[k][0] == 1.0
    // Column indexing follows row-major order and matrix elements are products of Hermite polynomials
    ensures forall k :: 0 <= k < |V| ==>
        forall i, j :: 0 <= i <= xdeg && 0 <= j <= ydeg ==>
            (ydeg + 1) * i + j < |V[k]| && V[k][(ydeg + 1) * i + j] == HermitePolynomial(i, x[k]) * HermitePolynomial(j, y[k])
    // Coefficient ordering property: each index corresponds to correct i,j pair
    ensures forall k :: 0 <= k < |V| ==>
        forall idx {:trigger idx / (ydeg + 1)} :: 0 <= idx < |V[k]| ==>
            idx / (ydeg + 1) <= xdeg && idx % (ydeg + 1) <= ydeg && idx == (ydeg + 1) * (idx / (ydeg + 1)) + (idx % (ydeg + 1))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): build Vandermonde using HermitePolynomial_exec with explicit decreases and exec-based invariants */
  var n := |x|;
  var cols := (xdeg + 1) * (ydeg + 1);
  var Varr := new seq<real>[n];
  var k := 0;
  while k < n
    decreases n - k
    invariant 0 <= k <= n
    invariant forall t :: 0 <= t < k ==> (|Varr[t]| == cols && (forall idx :: 0 <= idx < cols ==> Varr[t][idx] == HermitePolynomial_exec(idx / (ydeg + 1), x[t]) * HermitePolynomial_exec(idx % (ydeg + 1), y[t])))
  {
    var rowArr := new real[cols];
    var idx := 0;
    while idx < cols
      decreases cols - idx
      invariant 0 <= idx <= cols
      invariant forall u :: 0 <= u < idx ==> rowArr[u] == HermitePolynomial_exec(u / (ydeg + 1), x[k]) * HermitePolynomial_exec(u % (ydeg + 1), y[k])
    {
      var i := idx / (ydeg + 1);
      var j := idx % (ydeg + 1);
      var hi := HermitePolynomial_exec(i, x[k]);
      var hj := HermitePolynomial_exec(j, y[k]);
      HermitePolynomial_match(i, x[k]);
      HermitePolynomial_match(j, y[k]);
      rowArr[idx] := hi * hj;
      idx := idx + 1;
    }
    Varr[k] := rowArr[..];
    k := k + 1;
  }
  V := Varr[..];
}

// </vc-code>
