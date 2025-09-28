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
/* helper modified by LLM (iteration 2): added postconditions to LagDerM for verification, and fixed index out of range in LagDerOnce */
function LagDerOnce(c: seq<real>): seq<real>
{
  var n := |c|;
  seq(n, i => (if i + 1 < n then -c[i + 1] else 0.0))
}

function LagDerM(c: seq<real>, m: nat): seq<real> decreases m
  ensures m == 0 ==> result == c
  ensures m > 0 ==> |result| == |c|
  ensures m >= |c| && |c| > 0 ==> forall i :: 0 <= i < |result| ==> result[i] == 0.0
{
  if m == 0 then c else LagDerOnce(LagDerM(c, m - 1))
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
  /* code modified by LLM (iteration 2): implementation of LagDer using helper LagDerM and scaling */
  if m == 0 {
    result := c;
  } else {
    var base := LagDerM(c, m);
    result := seq(|c|, i => base[i] * pow(scl, m));
  }
}
// </vc-code>
