// <vc-preamble>
// Method to differentiate a Laguerre series
// Helper function for power computation (assumed to exist)
function pow(base: real, exp: nat): real
  decreases exp
{
  if exp == 0 then 1.0
  else base * pow(base, exp - 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix DifferentiateOnce sequence comprehension syntax */
function DifferentiateOnce(c: seq<real>, k: nat): seq<real>
  requires k <= |c|
  ensures |DifferentiateOnce(c, k)| == |c|
  ensures forall i :: 0 <= i < |c| ==> if i < k then DifferentiateOnce(c, k)[i] == 0.0 else DifferentiateOnce(c, k)[i] == c[i] * (i - k + 1)
{
  if k == 0 then c else seq(i: int | 0 <= i < |c|, if i < k then 0.0 else c[i] * (i - k + 1))
}

function DifferentiateRepeatedly(c: seq<real>, m: nat): seq<real>
  requires m <= |c|
  ensures |DifferentiateRepeatedly(c, m)| == |c|
  ensures m == 0 ==> DifferentiateRepeatedly(c, m) == c
  ensures forall i :: 0 <= i < |c| ==> (if i < m then DifferentiateRepeatedly(c, m)[i] == 0.0 else DifferentiateRepeatedly(c, m)[i] == fact_div(i, m) * c[i])
  decreases m
{
  if m == 0 then c
  else DifferentiateOnce(DifferentiateRepeatedly(c, m-1), m-1)
}

function fact(n: nat): real
  decreases n
{
  if n == 0 then 1.0
  else n.toReal() * fact(n - 1)
}

function fact_div(n: nat, k: nat): real
  requires k <= n
{
  if k == 0 then 1.0
  else (n - k + 1).toReal() * fact_div(n, k - 1)
}
// </vc-helpers>

// <vc-spec>
method {:axiom} LagDer(c: seq<real>, m: nat, scl: real) returns (result: seq<real>)
  requires true
  ensures |result| == |c|
  // If m = 0, no differentiation occurs - result equals input scaled by scl^0 = 1
  ensures m == 0 ==> result == c
  // For over-differentiation (m >= degree + 1), result becomes zero
  ensures m >= |c| && |c| > 0 ==> 
    forall i :: 0 <= i < |result| ==> result[i] == 0.0
  // For main differentiation case (0 < m < |c|), result is scaled by scl^m
  ensures 0 < m < |c| && scl != 0.0 ==> 
    exists base_result: seq<real> :: (|base_result| == |c| &&
    (forall i :: 0 <= i < |result| ==> result[i] == base_result[i] * pow(scl, m)))
  // When scl = 0 and m > 0, result is zero (since scl^m = 0)
  ensures m > 0 && scl == 0.0 ==> 
    forall i :: 0 <= i < |result| ==> result[i] == 0.0
  // Scaling property: differentiating with scl=1 then scaling is equivalent to direct scaling
  ensures m > 0 && |c| > m ==> 
    (forall base: seq<real> :: |base| == |c| ==> 
     forall i :: 0 <= i < |result| ==> result[i] == base[i] * pow(scl, m))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fix zero initialization issues */
  if m == 0 {
    result := c;
  } else if m >= |c| || scl == 0.0 {
    result := new real[|c|];
    var i := 0;
    while i < |c|
      invariant i <= |c|
      invariant forall j :: 0 <= j < i ==> result[j] == 0.0
    {
      result[i] := 0.0;
      i := i + 1;
    }
  } else {
    var base_result := DifferentiateRepeatedly(c, m);
    result := new real[|c|];
    var i := 0;
    while i < |c|
      invariant i <= |c|
      invariant forall j :: 0 <= j < i ==> result[j] == base_result[j] * pow(scl, m)
    {
      result[i] := base_result[i] * pow(scl, m);
      i := i + 1;
    }
  }
}
// </vc-code>
