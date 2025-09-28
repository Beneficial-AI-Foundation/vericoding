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
function add(p: seq<real>, q: seq<real>): seq<real>
  decreases |p| + |q|
{
  if |p| == 0 then q
  else if |q| == 0 then p
  else [p[0] + q[0]] + add(p[1..], q[1..])
}

function scale(a: real, p: seq<real>): seq<real>
  decreases |p|
{
  if |p| == 0 then []
  else [a * p[0]] + scale(a, p[1..])
}

function shiftX(p: seq<real>): seq<real>
{
  [0.0] + p
}

function PolyOfLegendre(n: nat): seq<real>
  decreases n
{
  if n == 0 then [1.0]
  else if n == 1 then [0.0, 1.0]
  else add(
         scale(((2.0 * (n-1) as real + 1.0) / (n as real)), shiftX(PolyOfLegendre(n-1))),
         scale(-((n-1) as real / (n as real)), PolyOfLegendre(n-2))
       )
}

function LegendreSeriesPoly(c: seq<real>, k: nat): seq<real>
  decreases |c|
{
  if |c| == 0 then []
  else add(scale(c[0], PolyOfLegendre(k)), LegendreSeriesPoly(c[1..], k+1))
}

lemma lemma_Eval_add(p: seq<real>, q: seq<real>, x: real)
  ensures EvaluatePolynomial(add(p,q), x) == EvaluatePolynomial(p,x) + EvaluatePolynomial(q,x)
  decreases |p| + |q|
{
  if |p| == 0 || |q| == 0 {
  } else {
    lemma_Eval_add(p[1..], q[1..], x);
  }
}

lemma lemma_Eval_scale(a: real, p: seq<real>, x: real)
  ensures EvaluatePolynomial(scale(a,p), x) == a * EvaluatePolynomial(p,x)
  decreases |p|
{
  if |p| == 0 {
  } else {
    lemma_Eval_scale(a, p[1..], x);
  }
}

/* helper modified by LLM (iteration 2): implemented evaluation property for shiftX */
lemma lemma_Eval_shift(p: seq<real>, x: real)
  ensures EvaluatePolynomial(shiftX(p), x) == x * EvaluatePolynomial(p,x)
{
  // shiftX(p) == [0.0] + p
  if |p| == 0 {
    // LHS: EvaluatePolynomial([0.0], x) == 0.0, RHS: x * 0.0 == 0.0
  } else {
    // |[0.0] + p| == |p| + 1 > 1, so the recursive branch applies
  }
}

lemma lemma_Len_add(p: seq<real>, q: seq<real>)
  ensures |add(p,q)| == (if |p| >= |q| then |p| else |q|)
  decreases |p| + |q|
{
  if |p| == 0 || |q| == 0 {
  } else {
    lemma_Len_add(p[1..], q[1..]);
  }
}

lemma lemma_Len_scale(a: real, p: seq<real>)
  ensures |scale(a,p)| == |p|
  decreases |p|
{
  if |p| == 0 {
  } else {
    lemma_Len_scale(a, p[1..]);
  }
}

/* helper modified by LLM (iteration 2): proved length property for shiftX */
lemma lemma_Len_shift(p: seq<real>)
  ensures |shiftX(p)| == |p| + 1
{
  // shiftX(p) = [0.0] + p, so length increases by 1
}

lemma lemma_Poly_len(n: nat)
  ensures |PolyOfLegendre(n)| == n + 1
  decreases n
{
  if n == 0 {
  } else if n == 1 {
  } else {
    lemma_Poly_len(n-1);
    lemma_Poly_len(n-2);
    lemma_Len_shift(PolyOfLegendre(n-1));
    lemma_Len_scale(((2.0 * (n-1) as real + 1.0) / (n as real)), shiftX(PolyOfLegendre(n-1)));
    lemma_Len_scale(-((n-1) as real / (n as real)), PolyOfLegendre(n-2));
    lemma_Len_add(scale(((2.0 * (n-1) as real + 1.0) / (n as real)), shiftX(PolyOfLegendre(n-1))), scale(-((n-1) as real / (n as real)), PolyOfLegendre(n-2)));
  }
}

lemma lemma_Poly_correct(n: nat, x: real)
  ensures EvaluatePolynomial(PolyOfLegendre(n), x) == LegendrePolynomial(n, x)
  decreases n
{
  if n == 0 {
  } else if n == 1 {
  } else {
    lemma_Poly_correct(n-1, x);
    lemma_Poly_correct(n-2, x);
    lemma_Eval_shift(PolyOfLegendre(n-1), x);
    lemma_Eval_scale(((2.0 * (n-1) as real + 1.0) / (n as real)), shiftX(PolyOfLegendre(n-1)), x);
    lemma_Eval_scale(-((n-1) as real / (n as real)), PolyOfLegendre(n-2), x);
    lemma_Eval_add(scale(((2.0 * (n-1) as real + 1.0) / (n as real)), shiftX(PolyOfLegendre(n-1))), scale(-((n-1) as real / (n as real)), PolyOfLegendre(n-2)), x);
  }
}

lemma lemma_LSP_len(c: seq<real>, k: nat)
  ensures |LegendreSeriesPoly(c, k)| == (if |c| == 0 then 0 else k + |c|)
  decreases |c|
{
  if |c| == 0 {
  } else {
    lemma_Poly_len(k);
    lemma_LSP_len(c[1..], k+1);
    lemma_Len_scale(c[0], PolyOfLegendre(k));
    lemma_Len_add(scale(c[0], PolyOfLegendre(k)), LegendreSeriesPoly(c[1..], k+1));
  }
}

lemma lemma_LSP_correct(c: seq<real>, k: nat, x: real)
  ensures EvaluatePolynomial(LegendreSeriesPoly(c, k), x) == EvaluateLegendreHelper(c, x, k)
  decreases |c|
{
  if |c| == 0 {
  } else {
    lemma_Poly_correct(k, x);
    lemma_LSP_correct(c[1..], k+1, x);
    lemma_Eval_scale(c[0], PolyOfLegendre(k), x);
    lemma_Eval_add(scale(c[0], PolyOfLegendre(k)), LegendreSeriesPoly(c[1..], k+1), x);
  }
}

lemma lemma_EL_start(c: seq<real>, x: real)
  ensures EvaluateLegendre(c, x) == EvaluateLegendreHelper(c, x, 0)
  decreases |c|
{
  if |c| == 0 {
  } else {
    // By definition of EvaluateLegendre and EvaluateLegendreHelper at startIndex 0
  }
}

/* helper modified by LLM (iteration 2): established equivalence for sequences of length < 3 */
lemma lemma_small_equivalence(c: seq<real>, x: real)
  ensures |c| < 3 ==> EvaluateLegendre(c, x) == EvaluatePolynomial(c, x)
{
  if |c| == 0 {
    // 0 == 0
  } else if |c| == 1 {
    // EvaluateLegendre([a], x) = a * P0(x) + 0 = a
    assert EvaluateLegendre(c, x) == c[0] * LegendrePolynomial(0, x) + EvaluateLegendreHelper(c[1..], x, 1);
    assert LegendrePolynomial(0, x) == 1.0;
    assert c[1..] == [];
    assert EvaluateLegendreHelper([], x, 1) == 0.0;
    assert EvaluateLegendre(c, x) == c[0];
    // EvaluatePolynomial([a], x) = a
    assert |c| == 1;
    assert EvaluatePolynomial(c, x) == c[0];
  } else if |c| == 2 {
    // EvaluateLegendre([a,b], x) = a*P0(x) + b*P1(x) = a + b*x
    assert EvaluateLegendre(c, x) == c[0] * LegendrePolynomial(0, x) + EvaluateLegendreHelper(c[1..], x, 1);
    assert LegendrePolynomial(0, x) == 1.0;
    assert |c[1..]| == 1;
    assert EvaluateLegendreHelper(c[1..], x, 1) == c[1] * LegendrePolynomial(1, x) + EvaluateLegendreHelper([], x, 2);
    assert LegendrePolynomial(1, x) == x;
    assert EvaluateLegendreHelper([], x, 2) == 0.0;
    assert EvaluateLegendre(c, x) == c[0] + c[1] * x;
    // EvaluatePolynomial([a,b], x) = a + x*b
    assert EvaluatePolynomial([c[1]], x) == c[1];
    assert EvaluatePolynomial(c, x) == c[0] + x * EvaluatePolynomial([c[1]], x);
  } else {
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
{
  /* code modified by LLM (iteration 2): implement conversion via constructed polynomial and prove equivalence */
  if |c| < 3 {
    result := c;
    assert forall x :: EvaluatePolynomial(result, x) == EvaluateLegendre(c, x);
    forall x | true
      ensures EvaluatePolynomial(result, x) == EvaluateLegendre(c, x)
    {
      lemma_small_equivalence(c, x);
    }
  } else {
    result := LegendreSeriesPoly(c, 0);
    lemma_LSP_len(c, 0);
    assert forall x :: EvaluatePolynomial(result, x) == EvaluateLegendre(c, x);
    forall x | true
      ensures EvaluatePolynomial(result, x) == EvaluateLegendre(c, x)
    {
      lemma_LSP_correct(c, 0, x);
      lemma_EL_start(c, x);
    }
  }
}
// </vc-code>
