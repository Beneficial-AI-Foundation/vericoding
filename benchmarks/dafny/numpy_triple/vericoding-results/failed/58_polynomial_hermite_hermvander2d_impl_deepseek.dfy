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
function FillVandermondeRow(x_val: real, y_val: real, xdeg: nat, ydeg: nat): seq<real>
    requires xdeg >= 0 && ydeg >= 0
    ensures |result| == (xdeg + 1) * (ydeg + 1)
    ensures forall i, j :: 0 <= i <= xdeg && 0 <= j <= ydeg ==>
        (ydeg + 1) * i + j < |result| && result[(ydeg + 1) * i + j] == HermitePolynomial(i, x_val) * HermitePolynomial(j, y_val)
    ensures result[0] == 1.0
{
    /* helper modified by LLM (iteration 5): Fix variable naming and loop syntax */
    var size := (xdeg + 1) * (ydeg + 1);
    var row := seq(size, i => 0.0);
    var i: nat := 0;
    while i <= xdeg
        invariant 0 <= i <= xdeg+1
        invariant |row| == size
        invariant forall i0, j0 :: 0 <= i0 < i && 0 <= j0 <= ydeg ==>
            (ydeg + 1) * i0 + j0 < |row| && row[(ydeg + 1) * i0 + j0] == HermitePolynomial(i0, x_val) * HermitePolynomial(j0, y_val)
    {
        var j: nat := 0;
        while j <= ydeg
            invariant 0 <= j <= ydeg+1
            invariant |row| == size
            invariant forall j0 :: 0 <= j0 < j ==>
                (ydeg + 1) * i + j0 < |row| && row[(ydeg + 1) * i + j0] == HermitePolynomial(i, x_val) * HermitePolynomial(j0, y_val)
        {
            row := row[(ydeg + 1) * i + j := HermitePolynomial(i, x_val) * HermitePolynomial(j, y_val)];
            j := j + 1;
        }
        i := i + 1;
    }
    row
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
  /* code modified by LLM (iteration 5): Remove assignment statement and fix compilation */
  var n := |x|;
  V := [];
  
  var idx := 0;
  while idx < n
      invariant 0 <= idx <= n
      invariant |V| == idx
      invariant forall k :: 0 <= k < idx ==> |V[k]| == (xdeg + 1) * (ydeg + 1)
      invariant forall k :: 0 <= k < idx ==> V[k][0] == 1.0
      invariant forall k :: 0 <= k < idx ==>
          forall i, j :: 0 <= i <= xdeg && 0 <= j <= ydeg ==>
              (ydeg + 1) * i + j < |V[k]| && V[k][(ydeg + 1) * i + j] == HermitePolynomial(i, x[k]) * HermitePolynomial(j, y[k])
  {
      var row := FillVandermondeRow(x[idx], y[idx], xdeg, ydeg);
      V := V + [row];
      idx := idx + 1;
  }
}
// </vc-code>
