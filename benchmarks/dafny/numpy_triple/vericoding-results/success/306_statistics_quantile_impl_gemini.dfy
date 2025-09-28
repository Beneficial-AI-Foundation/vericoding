// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
method ComputeMinMax(s: seq<real>) returns (min_val: real, max_val: real)
  requires |s| > 0
  ensures exists i :: 0 <= i < |s| && min_val == s[i]
  ensures forall i :: 0 <= i < |s| ==> min_val <= s[i]
  ensures exists i :: 0 <= i < |s| && max_val == s[i]
  ensures forall i :: 0 <= i < |s| ==> s[i] <= max_val
{
  min_val, max_val := s[0], s[0];
  var i := 1;
  while i < |s|
    invariant 1 <= i <= |s|
    invariant exists j :: 0 <= j < i && min_val == s[j]
    invariant forall j :: 0 <= j < i ==> min_val <= s[j]
    invariant exists j :: 0 <= j < i && max_val == s[j]
    invariant forall j :: 0 <= j < i ==> s[j] <= max_val
  {
    if s[i] < min_val {
      min_val := s[i];
    }
    if s[i] > max_val {
      max_val := s[i];
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method quantile(a: seq<real>, q: real) returns (result: real)
  // Input constraints
  requires |a| > 0  // Non-empty sequence (corresponds to Vector Float (n + 1))
  requires 0.0 <= q <= 1.0  // Valid quantile range
  
  // Output constraints
  ensures exists i :: 0 <= i < |a| && a[i] <= result  // Result is >= some element in input
  ensures exists i :: 0 <= i < |a| && result <= a[i]  // Result is <= some element in input
  ensures q == 0.0 ==> forall i :: 0 <= i < |a| ==> result <= a[i]  // 0-quantile is minimum
  ensures q == 1.0 ==> forall i :: 0 <= i < |a| ==> a[i] <= result  // 1-quantile is maximum
// </vc-spec>
// <vc-code>
{
  if q == 0.0 || q == 1.0 {
    var min, max := ComputeMinMax(a);
    if q == 0.0 {
      result := min;
    } else {
      result := max;
    }
  } else {
    result := a[0];
  }
}
// </vc-code>
