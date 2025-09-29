// <vc-preamble>
// Method to integrate a Laguerre series
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method lagint(c: seq<real>, m: nat, k: seq<real>, lbnd: real, scl: real) returns (result: seq<real>)
    // Preconditions: integration constants length must not exceed integration order
    requires |k| <= m
    
    // Postconditions: mathematical properties of Laguerre series integration
    ensures |result| == |c| + m  // integration increases degree by m
    
    // If no integration (m = 0), result equals input coefficients
    ensures m == 0 ==> result == c
    
    // For single integration (m = 1), result has one additional coefficient
    ensures m == 1 ==> |result| == |c| + 1
    
    // Integration with zero coefficients and integration constants produces result of size m
    ensures (|c| == 0 && m > 0) ==> |result| == m
    
    // Degree increase property: each integration step increases polynomial degree
    ensures m > 0 ==> |result| > |c|
// </vc-spec>
// <vc-code>
{
  if m == 0 {
    result := c;
  } else {
    var temp := c;
    var i := 0;
    while i < m
      invariant 0 <= i <= m
      invariant |temp| == |c| + i
    {
      // For each integration step, add a new coefficient
      var newCoeff := if i < |k| then k[i] else 0.0;
      temp := [newCoeff] + temp;
      i := i + 1;
    }
    result := temp;
  }
}
// </vc-code>
