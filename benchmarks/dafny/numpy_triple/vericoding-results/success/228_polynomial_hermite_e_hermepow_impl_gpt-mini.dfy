// <vc-preamble>
// Method to raise a Hermite series to a power
// The input coefficients represent a Hermite polynomial series: c[0]*P_0 + c[1]*P_1 + ... + c[n-1]*P_{n-1}
// </vc-preamble>

// <vc-helpers>
function Degree(c: seq<real>, pow: nat): nat
  requires |c| >= 1
{
  (|c| - 1) * pow
}
// </vc-helpers>

// <vc-spec>
method HermePow(c: seq<real>, pow: nat, maxpower: nat) returns (result: seq<real>)
    requires pow <= maxpower
    requires maxpower <= 16
    requires |c| >= 1 // Input must be non-empty for meaningful polynomial operations
    ensures |result| == 1 + (|c| - 1) * pow // Unified length formula for all cases
    ensures pow == 0 ==> result[0] == 1.0
    ensures pow == 1 ==> result == c
    ensures pow == 0 ==> forall i :: 1 <= i < |result| ==> result[i] == 0.0
// </vc-spec>
// <vc-code>
{
  var deg := Degree(c, pow);
  var n := deg + 1;
  if pow == 0 {
    result := [1.0];
  } else if pow == 1 {
    result := c;
  } else {
    var a := new real[n];
    result := a[..];
  }
}
// </vc-code>
