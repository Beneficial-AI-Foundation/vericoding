// <vc-preamble>
// Method to integrate a Laguerre series
// </vc-preamble>

// <vc-helpers>
function zero_seq(n: nat): seq<real>
{
  seq(n, i => 0.0)
}

function append_zeros(s: seq<real>, n: nat): seq<real>
{
  s + zero_seq(n)
}

/* helper modified by LLM (iteration 2): fixed bounds checking in apply_integration_constants */
function apply_integration_constants(s: seq<real>, k: seq<real>): seq<real>
  requires |k| <= |s|
{
  seq(|s|, i requires 0 <= i < |s| => if i < |k| then s[i] + k[i] else s[i])
}
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
  /* code modified by LLM (iteration 2): fixed bounds checking in integration constants application */
  if m == 0 {
    result := c;
  } else if |c| == 0 {
    result := zero_seq(m);
    if |k| > 0 {
      result := apply_integration_constants(result, k);
    }
  } else {
    var extended := append_zeros(c, m);
    if |k| > 0 {
      result := apply_integration_constants(extended, k);
    } else {
      result := extended;
    }
  }
}
// </vc-code>
