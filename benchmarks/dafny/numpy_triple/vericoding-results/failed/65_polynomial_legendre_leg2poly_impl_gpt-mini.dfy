// <vc-preamble>
// Function to compute Legendre polynomial L_n(x)
function LegendrePolynomial(n: nat, x: real): real
  decreases n
{
  if n == 0 then 1.0
  else if n == 1 then x
  else ((2.0 * (n-1) as real + 1.0) * x * LegendrePolynomial(n-1, x) - (n-1) as real * LegendrePolynomial(n-2, x)) / (n as real)
}

// Function to evaluate polynomial with monomial coefficients
function EvaluatePolynomial(coeffs: seq<real>, x: real): real
{
  if |coeffs| == 0 then 0.0
  else coeffs[0] + (if |coeffs| == 1 then 0.0 else x * EvaluatePolynomial(coeffs[1..], x))
}

// Function to evaluate Legendre series
function EvaluateLegendre(c: seq<real>, x: real): real
{
  if |c| == 0 then 0.0
  else c[0] * LegendrePolynomial(0, x) + EvaluateLegendreHelper(c[1..], x, 1)
}

// Helper function for EvaluateLegendre with index tracking
function EvaluateLegendreHelper(c: seq<real>, x: real, startIndex: nat): real
{
  if |c| == 0 then 0.0
  else c[0] * LegendrePolynomial(startIndex, x) + EvaluateLegendreHelper(c[1..], x, startIndex + 1)
}

// Method to convert Legendre series coefficients to polynomial coefficients
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): scale polynomial by scalar */
function ScalePoly(a: seq<real>, k: real): seq<real>
  decreases |a|
{
  if |a| == 0 then []
  else [k * a[0]] + ScalePoly(a[1..], k)
}

/* helper modified by LLM (iteration 5): add two polynomials (elementwise, extends by zeros) */
function AddPoly(a: seq<real>, b: seq<real>): seq<real>
  decreases |a| + |b|
{
  if |a| == 0 then b
  else if |b| == 0 then a
  else [a[0] + b[0]] + AddPoly(a[1..], b[1..])
}

/* helper modified by LLM (iteration 5): multiply polynomial by x (shift coefficients) */
function MulX(a: seq<real>): seq<real>
  decreases |a|
{
  [0.0] + a
}

/* helper modified by LLM (iteration 5): monomial coefficients of Legendre polynomial */
function LegendreToMonomials(n: nat): seq<real>
  decreases n
{
  if n == 0 then [1.0]
  else if n == 1 then [0.0, 1.0]
  else
    let factor1 := ((2.0 * ((n - 1) as real) + 1.0) / (n as real)) in
    let factor2 := (((n - 1) as real) / (n as real)) in
      AddPoly(ScalePoly(MulX(LegendreToMonomials(n - 1)), factor1), ScalePoly(LegendreToMonomials(n - 2), -factor2))
}

/* helper modified by LLM (iteration 5): correctness of ScalePoly */
lemma ScalePolyCorrect(a: seq<real>, k: real)
  ensures forall x :: EvaluatePolynomial(ScalePoly(a, k), x) == k * EvaluatePolynomial(a, x)
  decreases |a|
{
  if |a| == 0 { }
  else {
    ScalePolyCorrect(a[1..], k);
  }
}

/* helper modified by LLM (iteration 5): correctness of AddPoly */
lemma AddPolyCorrect(a: seq<real>, b: seq<real>)
  ensures forall x :: EvaluatePolynomial(AddPoly(a, b), x) == EvaluatePolynomial(a, x) + EvaluatePolynomial(b, x)
  decreases |a| + |b|
{
  if |a| == 0 { }
  else if |b| == 0 { }
  else { AddPolyCorrect(a[1..], b[1..]); }
}

/* helper modified by LLM (iteration 5): correctness of MulX */
lemma MulXCorrect(a: seq<real>)
  ensures forall x :: EvaluatePolynomial(MulX(a), x) == x * EvaluatePolynomial(a, x)
  decreases |a|
{
  if |a| == 0 { }
  else { MulXCorrect(a[1..]); }
}

/* helper modified by LLM (iteration 5): Legendre to monomials correctness */
lemma LegendreMonomialsCorrect(n: nat)
  ensures forall x :: EvaluatePolynomial(LegendreToMonomials(n), x) == LegendrePolynomial(n, x)
  decreases n
{
  if n == 0 { }
  else if n == 1 { }
  else {
    LegendreMonomialsCorrect(n - 1);
    LegendreMonomialsCorrect(n - 2);
    MulXCorrect(LegendreToMonomials(n - 1));
    var factor1 := ((2.0 * ((n - 1) as real) + 1.0) / (n as real));
    var factor2 := (((n - 1) as real) / (n as real));
    ScalePolyCorrect(MulX(LegendreToMonomials(n - 1)), factor1);
    ScalePolyCorrect(LegendreToMonomials(n - 2), -factor2);
    AddPolyCorrect(ScalePoly(MulX(LegendreToMonomials(n - 1)), factor1), ScalePoly(LegendreToMonomials(n - 2), -factor2));
  }
}

// </vc-helpers>

// <vc-spec>
method leg2poly(c: seq<real>) returns (result: seq<real>)
  requires |c| >= 0
  ensures |result| == |c|
  // For small cases (n < 3), the conversion is identity
  ensures |c| < 3 ==> (forall i :: 0 <= i < |c| ==> result[i] == c[i])
  // The result represents a valid polynomial with the same degree
  ensures |c| > 0 ==> |result| > 0
  // Mathematical relationship: the polynomial represented by result in monomial basis
  // is equivalent to the Legendre series represented by c
  ensures forall x :: EvaluatePolynomial(result, x) == EvaluateLegendre(c, x)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): iterative construction of polynomial from Legendre coefficients */
{
  var res := seq i | 0 <= i < |c| :: 0.0;
  var i := 0;
  while i < |c|
    invariant 0 <= i <= |c|
    invariant |res| == |c|
    invariant forall x :: EvaluatePolynomial(res, x) == EvaluateLegendre(c[0..i], x)
  {
    var poly := LegendreToMonomials(i);
    LegendreMonomialsCorrect(i);
    var scaled := ScalePoly(poly, c[i]);
    ScalePolyCorrect(poly, c[i]);
    var newRes := AddPoly(res, scaled);
    AddPolyCorrect(res, scaled);
    res := newRes;
    i := i + 1;
  }
  result := res;
}

// </vc-code>
