// <vc-preamble>
// Method to raise a Laguerre series to a specified power
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): trivial placeholder lemma to enable helper section */
lemma LagPow_Helpers() ensures true {
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
{
  /* code modified by LLM (iteration 2): handle pow==1 early and compute truncated convolution power */
  var n := |c|;
  if pow == 1 {
    result := c;
    return;
  }

  var resArr := new real[n];
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant forall i :: 0 <= i < k ==> resArr[i] == c[i]
  {
    resArr[k] := c[k];
    k := k + 1;
  }

  var temp := new real[n];
  var p := 1;
  while p < pow
    invariant 1 <= p <= pow
  {
    k := 0;
    while k < n
      invariant 0 <= k <= n
    {
      var s := 0.0;
      var j := 0;
      while j <= k
        invariant 0 <= j <= k + 1
      {
        // j and k-j are within bounds because k < n and 0 <= j <= k
        s := s + resArr[j] * c[k - j];
        j := j + 1;
      }
      temp[k] := s;
      k := k + 1;
    }

    k := 0;
    while k < n
      invariant 0 <= k <= n
    {
      resArr[k] := temp[k];
      k := k + 1;
    }

    p := p + 1;
  }

  result := resArr[..];
}
// </vc-code>
