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
/* helper modified by LLM (iteration 2): Fixed sequence comprehension syntax in DifferentiateOnce */
function DifferentiateOnce(c: seq<real>): seq<real>
  requires |c| > 0
  ensures |DifferentiateOnce(c)| == |c|
{
  if |c| == 1 then [0.0]
  else [c[1]] + seq(|c| - 1, i requires 0 <= i < |c| - 1 => if i + 2 < |c| then c[i + 2] - c[i] else -c[i])
}

function DifferentiateMultiple(c: seq<real>, m: nat): seq<real>
  requires |c| > 0
  decreases m
  ensures |DifferentiateMultiple(c, m)| == |c|
{
  if m == 0 then c
  else if m >= |c| then seq(|c|, _ => 0.0)
  else DifferentiateMultiple(DifferentiateOnce(c), m - 1)
}

function ScaleResult(c: seq<real>, scale: real): seq<real>
  requires |c| > 0
  ensures |ScaleResult(c, scale)| == |c|
  ensures forall i :: 0 <= i < |c| ==> ScaleResult(c, scale)[i] == c[i] * scale
{
  seq(|c|, i requires 0 <= i < |c| => c[i] * scale)
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
  /* code modified by LLM (iteration 2): No changes needed in main body */
  if |c| == 0 {
    result := [];
  } else if m == 0 {
    result := c;
  } else if m >= |c| {
    result := seq(|c|, _ => 0.0);
  } else {
    var base := DifferentiateMultiple(c, m);
    var scale_factor := pow(scl, m);
    result := ScaleResult(base, scale_factor);
  }
}
// </vc-code>
