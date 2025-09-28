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
/* helper modified by LLM (iteration 5): retained helper function and lemma for Hermite polynomial to support main implementation */
function hermitePoly(degree: nat, t: real): real
decreases degree
{
    if degree == 0 then 1.0
    else if degree == 1 then 2.0 * t
    else 2.0 * t * hermitePoly(degree - 1, t) - 2.0 * (degree - 1) as real * hermitePoly(degree - 2, t)
}

lemma HermitePolyEq(degree: nat, t: real)
ensures hermitePoly(degree, t) == HermitePolynomial(degree, t)
{
    var i := degree;
    if i == 0 {}
    else if i == 1 {}
    else {
        HermitePolyEq(degree - 1, t);
        HermitePolyEq(degree - 2, t);
    }
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
  /* code modified by LLM (iteration 5): fixed for loop syntax to Dafny style using 'to' for range */
  var res: seq<seq<real>> := [];
  for var k := 0 to |x| {
    var row: seq<real> := [];
    for var i := 0 to xdeg + 1 {
      for var j := 0 to ydeg + 1 {
        var val := hermitePoly(i, x[k]) * hermitePoly(j, y[k]);
        row := row + [val];
      }
    }
    res := res + [row];
  }
  V := res;
  // To use the lemma for postcondition verification
  forall k :: 0 <= k < |x| {
    forall i :: 0 <= i <= xdeg {
      forall j :: 0 <= j <= ydeg {
        HermitePolyEq(i, x[k]);
        HermitePolyEq(j, y[k]);
      }
    }
  }
}
// </vc-code>
