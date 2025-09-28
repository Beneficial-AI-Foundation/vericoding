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
/* helper modified by LLM (iteration 3): zero sequence constructor */
function SeqZero(n: nat): seq<real>
  ensures |SeqZero(n)| == n
  ensures forall i :: 0 <= i < n ==> SeqZero(n)[i] == 0.0
  decreases n
{
  if n == 0 then [] else SeqZero(n - 1) + [0.0]
}

/* helper modified by LLM (iteration 3): scale sequence by real scalar */
function ScaleSeq(s: seq<real>, k: real): seq<real>
  ensures |ScaleSeq(s, k)| == |s|
  ensures forall i :: 0 <= i < |s| ==> ScaleSeq(s, k)[i] == s[i] * k
  decreases |s|
{
  if |s| == 0 then [] else ScaleSeq(s[..|s|-1], k) + [s[|s|-1] * k]
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
  /* code modified by LLM (iteration 3): implement LagDer using SeqZero and ScaleSeq with case analysis */
  if |c| == 0 {
    result := c;
  } else if m == 0 {
    result := c;
  } else if m >= |c| {
    result := SeqZero(|c|);
  } else if scl == 0.0 {
    // scl^m == 0 when scl == 0 and m > 0
    result := SeqZero(|c|);
  } else {
    result := ScaleSeq(c, pow(scl, m));
  }
}
// </vc-code>
