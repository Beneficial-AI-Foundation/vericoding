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
/* helper modified by LLM (iteration 2): changed function method to function and fixed array construction */
function SuffixSum(c: seq<real>, start: nat): real
  requires 0 <= start < |c|
  decreases |c| - start
{
  if start == |c|-1 then c[start]
  else c[start] + SuffixSum(c, start+1)
}

/* helper modified by LLM (iteration 2): changed function method to function and fixed array construction */
function DifferentiateOnce(c: seq<real>): seq<real>
  requires |c| >= 1
  ensures |DifferentiateOnce(c)| == |c|
{
  if |c| == 1 then [0.0]
  else
      var n := |c|;
      [i <- 0..n-1 :: if i < n-1 then -SuffixSum(c, i+1) else 0.0]
}

/* helper modified by LLM (iteration 2): changed function method to function */
function ComputeLaguerreDerivative(c: seq<real>, m: nat): seq<real>
  requires 0 < m < |c|
  ensures |ComputeLaguerreDerivative(c, m)| == |c|
{
  if m == 1 then DifferentiateOnce(c)
  else ComputeLaguerreDerivative(DifferentiateOnce(c), m-1)
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
/* code modified by LLM (iteration 2): replaced array constructors with sequence comprehensions */
{
  if m == 0 {
    result := c;
  } else if m >= |c| {
    result := [i <- 0..(|c|-1) :: 0.0];
  } else {
    if scl == 0.0 {
      result := [i <- 0..(|c|-1) :: 0.0];
    } else {
      var base_result := ComputeLaguerreDerivative(c, m);
      var factor := pow(scl, m);
      result := [i <- 0..(|c|-1) :: base_result[i] * factor];
    }
  }
}
// </vc-code>
