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
/* helper modified by LLM (iteration 5): executable Hermite polynomial matching ghost version */
function method HermitePolynomialExec(degree: nat, t: real): real
  decreases degree
{
  if degree == 0 then 1.0
  else if degree == 1 then 2.0 * t
  else 2.0 * t * HermitePolynomialExec(degree - 1, t) - 2.0 * (degree - 1) as real * HermitePolynomialExec(degree - 2, t)
}

/* helper modified by LLM (iteration 5): proof that executable and ghost Hermite polynomials coincide */
lemma HermiteExecEqualsGhost(degree: nat, t: real)
  ensures HermitePolynomialExec(degree, t) == HermitePolynomial(degree, t)
  decreases degree
{
  if degree == 0 {
    assert HermitePolynomialExec(0, t) == 1.0;
    assert HermitePolynomial(0, t) == 1.0;
  } else if degree == 1 {
    assert HermitePolynomialExec(1, t) == 2.0 * t;
    assert HermitePolynomial(1, t) == 2.0 * t;
  } else {
    HermiteExecEqualsGhost(degree - 1, t);
    HermiteExecEqualsGhost(degree - 2, t);
    assert HermitePolynomialExec(degree, t) ==
      2.0 * t * HermitePolynomialExec(degree - 1, t) -
      2.0 * (degree - 1) as real * HermitePolynomialExec(degree - 2, t);
    assert HermitePolynomial(degree, t) ==
      2.0 * t * HermitePolynomial(degree - 1, t) -
      2.0 * (degree - 1) as real * HermitePolynomial(degree - 2, t);
  }
}

/* helper modified by LLM (iteration 5): lemma about div/mod bounds and decomposition for linear indexing */
lemma DivModProps(idx: nat, ydeg: nat, xdeg: nat)
  requires ydeg + 1 > 0
  requires idx < (xdeg + 1) * (ydeg + 1)
  ensures idx / (ydeg + 1) <= xdeg
  ensures idx % (ydeg + 1) <= ydeg
  ensures idx == (ydeg + 1) * (idx / (ydeg + 1)) + (idx % (ydeg + 1))
{
  var m := ydeg + 1;
  var q := idx / m;
  var r := idx % m;
  assert 0 <= r < m;
  assert idx == q * m + r;
  assert r <= ydeg;
  assert idx < (xdeg + 1) * m;
  if q > xdeg {
    assert q >= xdeg + 1;
    assert q * m >= (xdeg + 1) * m;
    assert q * m <= idx;
    assert (xdeg + 1) * m <= idx;
    assert false;
  }
}

/* helper modified by LLM (iteration 5): lemma computing quotient and remainder for linear index (row-major) */
lemma DivModForLinearIndex(i: nat, j: nat, ydeg: nat)
  requires j <= ydeg
  ensures ((ydeg + 1) * i + j) / (ydeg + 1) == i
  ensures ((ydeg + 1) * i + j) % (ydeg + 1) == j
{
  var m := ydeg + 1;
  assert j < m;
  assert ((m * i + j) / m) == i;
  assert ((m * i + j) % m) == j;
}

/* helper modified by LLM (iteration 5): lemma that linear index is within row bounds */
lemma IndexBound(i: nat, j: nat, xdeg: nat, ydeg: nat)
  requires i <= xdeg && j <= ydeg
  ensures (ydeg + 1) * i + j < (xdeg + 1) * (ydeg + 1)
{
  var m := ydeg + 1;
  assert m > 0;
  assert j < m;
  assert m * i + j < m * (i + 1);
  if i < xdeg {
    assert m * (i + 1) <= m * (xdeg + 1);
  } else {
    assert i == xdeg;
    assert m * (i + 1) == m * (xdeg + 1);
  }
  assert m * i + j < m * (xdeg + 1);
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
  /* code modified by LLM (iteration 5): compute entries using executable Hermite function and prove relation to ghost function via lemma */
  var n := |x|;
  var M := (xdeg + 1) * (ydeg + 1);
  V := [];
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant |V| == k
    invariant forall t :: 0 <= t < |V| ==> |V[t]| == M
    invariant forall t :: 0 <= t < |V| ==> M > 0 ==> V[t][0] == 1.0
    invariant forall t :: 0 <= t < |V| ==>
        forall i, j :: 0 <= i <= xdeg && 0 <= j <= ydeg ==>
            (ydeg + 1) * i + j < |V[t]| && V[t][(ydeg + 1) * i + j] == HermitePolynomial(i, x[t]) * HermitePolynomial(j, y[t])
    invariant forall t :: 0 <= t < |V| ==>
        forall idx :: 0 <= idx < |V[t]| ==>
            idx / (ydeg + 1) <= xdeg && idx % (ydeg + 1) <= ydeg && idx == (ydeg + 1) * (idx / (ydeg + 1)) + (idx % (ydeg + 1))
  {
    var xv := x[k];
    var yv := y[k];

    var r: seq<real> := [];
    var idx := 0;
    while idx < M
      invariant 0 <= idx <= M
      invariant |r| == idx
      invariant forall h :: 0 <= h < |r| ==> r[h] == HermitePolynomialExec(h / (ydeg + 1), xv) * HermitePolynomialExec(h % (ydeg + 1), yv)
    {
      r := r + [HermitePolynomialExec(idx / (ydeg + 1), xv) * HermitePolynomialExec(idx % (ydeg + 1), yv)];
      idx := idx + 1;
    }

    assert |r| == M;
    if M > 0 {
      assert 0 < |r|;
      assert r[0] == HermitePolynomialExec(0, xv) * HermitePolynomialExec(0, yv);
      assert HermitePolynomialExec(0, xv) == 1.0;
      assert HermitePolynomialExec(0, yv) == 1.0;
      assert r[0] == 1.0;
    }

    forall i, j | 0 <= i <= xdeg && 0 <= j <= ydeg
      ensures (ydeg + 1) * i + j < |r| && r[(ydeg + 1) * i + j] == HermitePolynomial(i, xv) * HermitePolynomial(j, yv)
    {
      var lin := (ydeg + 1) * i + j;
      IndexBound(i, j, xdeg, ydeg);
      assert lin < M;
      assert lin < |r|;
      assert r[lin] == HermitePolynomialExec(lin / (ydeg + 1), xv) * HermitePolynomialExec(lin % (ydeg + 1), yv);
      DivModForLinearIndex(i, j, ydeg);
      assert lin / (ydeg + 1) == i;
      assert lin % (ydeg + 1) == j;
      HermiteExecEqualsGhost(i, xv);
      HermiteExecEqualsGhost(j, yv);
      assert HermitePolynomialExec(i, xv) == HermitePolynomial(i, xv);
      assert HermitePolynomialExec(j, yv) == HermitePolynomial(j, yv);
    }

    assert ydeg + 1 > 0;
    forall h | 0 <= h < |r|
      ensures h / (ydeg + 1) <= xdeg && h % (ydeg + 1) <= ydeg && h == (ydeg + 1) * (h / (ydeg + 1)) + (h % (ydeg + 1))
    {
      DivModProps(h as nat, ydeg, xdeg);
    }

    var oldLen := |V|;
    V := V + [r];
    k := k + 1;
  }
}
// </vc-code>
