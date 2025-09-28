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
/* helper modified by LLM (iteration 5): Added non-ghost function to compute Hermite polynomial values */
function ComputeHermite(degree: nat, t: real): real
    decreases degree
{
    if degree == 0 then 1.0
    else if degree == 1 then 2.0 * t
    else 2.0 * t * ComputeHermite(degree - 1, t) - 2.0 * (degree - 1) as real * ComputeHermite(degree - 2, t)
}

/* helper modified by LLM (iteration 5): Added lemma to connect non-ghost and ghost functions */
lemma HermiteEquivalence(degree: nat, t: real)
    ensures ComputeHermite(degree, t) == HermitePolynomial(degree, t)
{
    // Proof by induction on degree
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
  /* code modified by LLM (iteration 5): Enhanced loop invariants to verify all postconditions */
  V := [];
  var k := 0;
  while k < |x|
    invariant 0 <= k <= |x|
    invariant |V| == k
    invariant forall m :: 0 <= m < k ==> |V[m]| == (xdeg + 1) * (ydeg + 1)
    invariant forall m :: 0 <= m < k && (xdeg + 1) * (ydeg + 1) > 0 ==> V[m][0] == 1.0
    invariant forall m :: 0 <= m < k ==> forall i, j :: 0 <= i <= xdeg && 0 <= j <= ydeg ==>
        (ydeg + 1) * i + j < |V[m]| && V[m][(ydeg + 1) * i + j] == HermitePolynomial(i, x[m]) * HermitePolynomial(j, y[m])
    invariant forall m :: 0 <= m < k ==> forall idx :: 0 <= idx < |V[m]| ==>
        idx / (ydeg + 1) <= xdeg && idx % (ydeg + 1) <= ydeg && idx == (ydeg + 1) * (idx / (ydeg + 1)) + (idx % (ydeg + 1))
  {
    var row: seq<real> := [];
    var i := 0;
    
    while i <= xdeg
      invariant 0 <= i <= xdeg + 1
      invariant |row| == i * (ydeg + 1)
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= ydeg ==>
        (ydeg + 1) * ii + jj < |row| && row[(ydeg + 1) * ii + jj] == HermitePolynomial(ii, x[k]) * HermitePolynomial(jj, y[k])
      invariant i > 0 && ydeg >= 0 ==> row[0] == 1.0
      invariant forall idx :: 0 <= idx < |row| ==>
        idx / (ydeg + 1) <= xdeg && idx % (ydeg + 1) <= ydeg && idx == (ydeg + 1) * (idx / (ydeg + 1)) + (idx % (ydeg + 1))
    {
      var j := 0;
      while j <= ydeg
        invariant 0 <= j <= ydeg + 1
        invariant |row| == i * (ydeg + 1) + j
        invariant forall ii, jj :: 0 <= ii < i && 0 <= jj <= ydeg ==>
          (ydeg + 1) * ii + jj < |row| && row[(ydeg + 1) * ii + jj] == HermitePolynomial(ii, x[k]) * HermitePolynomial(jj, y[k])
        invariant forall jj :: 0 <= jj < j ==>
          (ydeg + 1) * i + jj < |row| && row[(ydeg + 1) * i + jj] == HermitePolynomial(i, x[k]) * HermitePolynomial(jj, y[k])
        invariant i == 0 && j > 0 ==> row[0] == 1.0
        invariant forall idx :: 0 <= idx < |row| ==>
          idx / (ydeg + 1) <= xdeg && idx % (ydeg + 1) <= ydeg && idx == (ydeg + 1) * (idx / (ydeg + 1)) + (idx % (ydeg + 1))
      {
        var val := ComputeHermite(i, x[k]) * ComputeHermite(j, y[k]);
        HermiteEquivalence(i, x[k]);
        HermiteEquivalence(j, y[k]);
        row := row + [val];
        j := j + 1;
      }
      i := i + 1;
    }
    
    V := V + [row];
    k := k + 1;
  }
}
// </vc-code>
