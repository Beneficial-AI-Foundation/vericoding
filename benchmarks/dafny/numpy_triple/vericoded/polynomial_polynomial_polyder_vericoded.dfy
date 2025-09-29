// <vc-preamble>
// Helper function to compute the factorial-like factor for polynomial differentiation
// Computes original_idx * (original_idx - 1) * ... * (original_idx - m + 1)
function factorial_factor(original_idx: nat, m: nat): real
  decreases m
{
  if m == 0 then 1.0
  else (original_idx - (m - 1)) as real * factorial_factor(original_idx, m - 1)
}

// Helper function to compute scaling factor scl^m
function scale_factor(scl: real, m: nat): real
  decreases m
{
  if m == 0 then 1.0
  else scl * scale_factor(scl, m - 1)
}

// Polynomial differentiation method
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method polyder(c: seq<real>, m: nat, scl: real) returns (result: seq<real>)
  requires m <= |c|
  ensures |result| == |c| - m
  ensures m == 0 ==> result == c
  ensures m > 0 ==> forall i :: 0 <= i < |result| ==> 
    result[i] == c[i + m] * factorial_factor(i + m, m) * scale_factor(scl, m)
// </vc-spec>
// <vc-code>
{
  if m == 0 {
    result := c;
  } else {
    result := [];
    var i := 0;
    while i < |c| - m
      invariant 0 <= i <= |c| - m
      invariant |result| == i
      invariant forall j :: 0 <= j < i ==> result[j] == c[j + m] * factorial_factor(j + m, m) * scale_factor(scl, m)
    {
      var coeff := c[i + m] * factorial_factor(i + m, m) * scale_factor(scl, m);
      result := result + [coeff];
      i := i + 1;
    }
  }
}
// </vc-code>
