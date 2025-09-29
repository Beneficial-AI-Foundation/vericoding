// <vc-preamble>
// Method to raise a Hermite series to a power
// The input coefficients represent a Hermite polynomial series: c[0]*P_0 + c[1]*P_1 + ... + c[n-1]*P_{n-1}
// </vc-preamble>

// <vc-helpers>

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
  if pow == 0 {
    var len := 1 + (|c| - 1) * pow;
    result := [1.0];
    var i := 1;
    while i < len
      invariant 1 <= i <= len
      invariant |result| == i
      invariant result[0] == 1.0
      invariant forall j :: 1 <= j < i ==> result[j] == 0.0
    {
      result := result + [0.0];
      i := i + 1;
    }
  } else if pow == 1 {
    result := c;
  } else {
    var len := 1 + (|c| - 1) * pow;
    result := c;
    var p := 1;
    while p < pow
      invariant 1 <= p <= pow
      invariant |result| == 1 + (|c| - 1) * p
    {
      var temp := [];
      var i := 0;
      while i < |result|
        invariant 0 <= i <= |result|
        invariant |temp| == i
      {
        var j := 0;
        var sum := 0.0;
        while j < |c| && j <= i
          invariant 0 <= j <= |c|
          invariant j <= i + 1
        {
          if i - j < |result| {
            sum := sum + c[j] * result[i - j];
          }
          j := j + 1;
        }
        temp := temp + [sum];
        i := i + 1;
      }
      var k := |result|;
      while k < |result| + |c| - 1
        invariant |result| <= k <= |result| + |c| - 1
        invariant |temp| == k
      {
        var j := 0;
        var sum := 0.0;
        while j < |c| && k - j < |result|
          invariant 0 <= j <= |c|
        {
          if k - j >= 0 && k - j < |result| {
            sum := sum + c[j] * result[k - j];
          }
          j := j + 1;
        }
        temp := temp + [sum];
        k := k + 1;
      }
      result := temp;
      p := p + 1;
    }
  }
}
// </vc-code>
