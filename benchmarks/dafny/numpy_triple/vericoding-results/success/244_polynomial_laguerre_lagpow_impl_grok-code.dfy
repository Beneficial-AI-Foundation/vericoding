// <vc-preamble>
// Method to raise a Laguerre series to a specified power
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed recursive calls in PolyMulCoeff to avoid invalid decreases and supported int parameters for seq usage; updated polyMul to include conditional call for precondition proof */
function PolyMulCoeff(a: seq<real>, b: seq<real>, k: int, i: int): real
  requires |a| == |b|
  requires 0 <= k < |a|
  requires 0 <= i <= |a|
  decreases |a| - i
{
  if i == |a| || i > k then 0.0
  else a[i] * b[k - i] + PolyMulCoeff(a, b, k, i + 1)
}

/* helper modified by LLM (iteration 3): Updated polyMul to use conditional call over k to ensure preconditions are provable */
function polyMul(a: seq<real>, b: seq<real>): seq<real>
  requires |a| == |b| > 0
  ensures |polyMul(a, b)| == |a|
{
  var len := |a|;
  seq(len, k => if 0 <= k && k < len then PolyMulCoeff(a, b, k, 0) else 0.0)
}
// </vc-helpers>

// <vc-spec>
method LagPow(c: seq<real>, pow: nat, maxpower: nat) returns (result: seq<real>)
    // Power must be positive
    requires pow > 0
    // Power must not exceed maximum allowed power
    requires pow <= maxpower
    // Maximum power is bounded to prevent unmanageable growth (default limit is 16)
    requires maxpower <= 16
    // Input coefficients sequence must be non-empty
    requires |c| > 0
    
    // Result maintains same length as input coefficient sequence
    ensures |result| == |c|
    // Identity property: raising to power 1 returns the original series
    ensures pow == 1 ==> result == c
    // The coefficients are ordered from low to high degree terms
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Added if statement for pow==1 to explicitly handle identity case and ensure postcondition proof */
{
  var len := |c|;
  if pow == 1 {
    result := c;
  } else {
    result := c;
    var i := 1;
    while i < pow
      invariant 1 <= i <= pow
      invariant |result| == len
    {
      result := polyMul(result, c);
      i := i + 1;
    }
  }
}
// </vc-code>
