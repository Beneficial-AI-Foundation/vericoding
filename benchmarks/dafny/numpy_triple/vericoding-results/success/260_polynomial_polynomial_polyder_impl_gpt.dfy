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
/* helper modified by LLM (iteration 3): compute the ith coefficient of the m-th derivative with scaling */
function derivCoeff(c: seq<real>, i: int, m: nat, scl: real): real
  requires 0 <= i
  requires i + m < |c|
{
  c[i + m] * factorial_factor(i + m, m) * scale_factor(scl, m)
}
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
  /* code modified by LLM (iteration 3): construct result via a loop instead of a sequence comprehension */
  if m == 0 {
    result := c;
  } else {
    var n := |c| - m;
    var res: seq<real> := [];
    var i: nat := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |res| == i
      invariant forall j :: 0 <= j < i ==> res[j] == derivCoeff(c, j, m, scl)
      decreases n - i
    {
      assert i + m < |c|;
      res := res + [derivCoeff(c, i, m, scl)];
      i := i + 1;
    }
    result := res;
  }
}
// </vc-code>
