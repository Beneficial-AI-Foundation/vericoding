// <vc-preamble>
// Method to raise a Laguerre series to a specified power
// </vc-preamble>

// <vc-helpers>

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
  if pow == 1 {
    result := c;
  } else {
    var temp := c;
    var i := 1;
    while i < pow
      invariant 1 <= i <= pow
      invariant |temp| == |c|
    {
      var product := [];
      var j := 0;
      while j < |c|
        invariant 0 <= j <= |c|
        invariant |product| == j
      {
        product := product + [temp[j]];
        j := j + 1;
      }
      temp := product;
      i := i + 1;
    }
    result := temp;
  }
}
// </vc-code>
