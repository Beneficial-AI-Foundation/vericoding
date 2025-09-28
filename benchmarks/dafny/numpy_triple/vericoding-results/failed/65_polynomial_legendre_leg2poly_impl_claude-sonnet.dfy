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
/* helper modified by LLM (iteration 5): added lemmas to prove polynomial evaluation equivalence */
// Helper function to get coefficient of x^k in Legendre polynomial L_n(x)
function LegendreCoeff(n: nat, k: nat): real
  decreases n
{
  if n == 0 then (if k == 0 then 1.0 else 0.0)
  else if n == 1 then (if k == 1 then 1.0 else 0.0)
  else if k > n then 0.0
  else
    var coeff1 := (2.0 * (n-1) as real + 1.0) / (n as real);
    var coeff2 := (n-1) as real / (n as real);
    (if k == 0 then 0.0 else coeff1 * LegendreCoeff(n-1, k-1)) + coeff1 * LegendreCoeff(n-1, k) - coeff2 * LegendreCoeff(n-2, k)
}

function Power(x: real, k: nat): real
{
  if k == 0 then 1.0
  else x * Power(x, k - 1)
}

// Lemma: Legendre polynomial can be expressed as sum of its coefficients
lemma LegendreAsSum(n: nat, x: real)
  ensures LegendrePolynomial(n, x) == PolynomialFromCoeffs(n, x)
{
  var k := 0;
  while k <= n
    invariant 0 <= k <= n + 1
  {
    k := k + 1;
  }
}

// Helper function to express Legendre polynomial as explicit sum
function PolynomialFromCoeffs(n: nat, x: real): real
{
  PolynomialFromCoeffsHelper(n, x, 0)
}

function PolynomialFromCoeffsHelper(n: nat, x: real, k: nat): real
{
  if k > n then 0.0
  else LegendreCoeff(n, k) * Power(x, k) + PolynomialFromCoeffsHelper(n, x, k + 1)
}

// Lemma: polynomial evaluation equivalence
lemma PolynomialEvaluationEquivalence(coeffs: seq<real>, x: real)
  ensures EvaluatePolynomial(coeffs, x) == EvaluatePolynomialPowers(coeffs, x, 0)
{
}

function EvaluatePolynomialPowers(coeffs: seq<real>, x: real, startPower: nat): real
{
  if |coeffs| == 0 then 0.0
  else coeffs[0] * Power(x, startPower) + EvaluatePolynomialPowers(coeffs[1..], x, startPower + 1)
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
  /* code modified by LLM (iteration 5): added lemma calls to establish postcondition */
  if |c| == 0 {
    result := [];
    return;
  }
  
  if |c| == 1 {
    result := [c[0]];
    assert forall x :: EvaluatePolynomial(result, x) == c[0] * 1.0 == c[0] * LegendrePolynomial(0, x) == EvaluateLegendre(c, x);
    return;
  }
  
  if |c| == 2 {
    result := [c[0], c[1]];
    assert forall x :: EvaluatePolynomial(result, x) == c[0] + c[1] * x == c[0] * LegendrePolynomial(0, x) + c[1] * LegendrePolynomial(1, x) == EvaluateLegendre(c, x);
    return;
  }
  
  var resultArray := new real[|c|];
  
  // Initialize result array to zeros
  var i := 0;
  while i < |c|
    invariant 0 <= i <= |c|
    invariant resultArray.Length == |c|
    invariant forall j :: 0 <= j < i ==> resultArray[j] == 0.0
  {
    resultArray[i] := 0.0;
    i := i + 1;
  }
  
  // For each Legendre coefficient c[n], add its contribution to the polynomial
  var n := 0;
  while n < |c|
    invariant 0 <= n <= |c|
    invariant resultArray.Length == |c|
  {
    if c[n] != 0.0 {
      // Add c[n] * L_n(x) to the polynomial
      var k := 0;
      while k <= n
        invariant 0 <= k <= n + 1
        invariant resultArray.Length == |c|
      {
        var coeff := LegendreCoeff(n, k);
        if k < resultArray.Length {
          resultArray[k] := resultArray[k] + c[n] * coeff;
        }
        k := k + 1;
      }
    }
    n := n + 1;
  }
  
  result := resultArray[..];
  
  // Establish postcondition using lemmas
  forall x {
    PolynomialEvaluationEquivalence(result, x);
    var j := 0;
    while j < |c|
      invariant 0 <= j <= |c|
    {
      LegendreAsSum(j, x);
      j := j + 1;
    }
  }
}
// </vc-code>
