// <vc-preamble>
// Method to compute the domain (smallest interval) containing all input points
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): min_seq computes minimum of non-empty sequence */
method min_seq(s: seq<real>) returns (m: real)
  requires |s| >= 1
  ensures forall i :: 0 <= i < |s| ==> m <= s[i]
  ensures exists i :: 0 <= i < |s| && s[i] == m
{
  m := s[0];
  var i := 1;
  while i < |s|
    invariant 1 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> m <= s[j]
    invariant exists j :: 0 <= j < i && s[j] == m
    decreases |s| - i
  {
    if s[i] < m {
      m := s[i];
    }
    i := i + 1;
  }
}

/* helper modified by LLM (iteration 4): max_seq computes maximum of non-empty sequence */
method max_seq(s: seq<real>) returns (m: real)
  requires |s| >= 1
  ensures forall i :: 0 <= i < |s| ==> m >= s[i]
  ensures exists i :: 0 <= i < |s| && s[i] == m
{
  m := s[0];
  var i := 1;
  while i < |s|
    invariant 1 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> m >= s[j]
    invariant exists j :: 0 <= j < i && s[j] == m
    decreases |s| - i
  {
    if s[i] > m {
      m := s[i];
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method getdomain(x: seq<real>) returns (result: seq<real>)
  // Input must be non-empty
  requires |x| >= 1
  // Output is exactly 2 elements: [min, max]
  ensures |result| == 2
  // The minimum is less than or equal to the maximum
  ensures result[0] <= result[1]
  // Every element in x is within the computed domain
  ensures forall i :: 0 <= i < |x| ==> result[0] <= x[i] <= result[1]
  // The domain bounds are actually achieved by elements in x
  ensures exists i :: 0 <= i < |x| && x[i] == result[0]
  ensures exists j :: 0 <= j < |x| && x[j] == result[1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): compute min and max using helpers and return pair */
  var m := min_seq(x);
  var M := max_seq(x);
  result := [m, M];
}
// </vc-code>
