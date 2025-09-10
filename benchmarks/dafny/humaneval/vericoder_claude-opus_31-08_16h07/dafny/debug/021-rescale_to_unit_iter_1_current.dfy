function affine(x: real, shift: real, scale: real) : real
    requires scale > 0.0
{
    (x + shift) / scale
}
function affine_seq(s: seq<real>, r: seq<real>, shift: real, scale: real) : bool
  requires scale > 0.0
  requires |r| == |s|
{
  forall i :: 0 <= i < |s| ==> r[i] == affine(s[i], shift, scale)
}

// <vc-helpers>
lemma affine_correctness(s: seq<real>, r: seq<real>, min_val: real, max_val: real)
  requires |s| == |r|
  requires max_val > min_val
  requires forall i :: 0 <= i < |s| ==> r[i] == (s[i] - min_val) / (max_val - min_val)
  ensures affine_seq(s, r, -min_val, max_val - min_val)
{
  assert forall i :: 0 <= i < |s| ==> r[i] == affine(s[i], -min_val, max_val - min_val);
}
// </vc-helpers>

// <vc-spec>
method rescale_to_unit(s: seq<real>) returns (r : seq<real>)
  // pre-conditions-start
  requires |s| >= 2
  requires exists i, j : int :: (0 <= i < j < |s|) && s[i] != s[j]
  // pre-conditions-end
  // post-conditions-start
  ensures |r| == |s|
  ensures forall i : int :: 0 <= i < |s| ==> 0.0 <= r[i] <= 1.0
  ensures exists i : int :: 0 <= i < |s| && r[i] == 0.0
  ensures exists i : int :: 0 <= i < |s| && r[i] == 1.0
  ensures exists shift, scale :: scale > 0.0 && affine_seq(s, r, shift, scale)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  // Find minimum value
  var min_val := s[0];
  var min_idx := 0;
  var i := 1;
  while i < |s|
    invariant 1 <= i <= |s|
    invariant 0 <= min_idx < |s|
    invariant min_val == s[min_idx]
    invariant forall j :: 0 <= j < i ==> min_val <= s[j]
  {
    if s[i] < min_val {
      min_val := s[i];
      min_idx := i;
    }
    i := i + 1;
  }
  
  // Find maximum value
  var max_val := s[0];
  var max_idx := 0;
  i := 1;
  while i < |s|
    invariant 1 <= i <= |s|
    invariant 0 <= max_idx < |s|
    invariant max_val == s[max_idx]
    invariant forall j :: 0 <= j < i ==> max_val >= s[j]
  {
    if s[i] > max_val {
      max_val := s[i];
      max_idx := i;
    }
    i := i + 1;
  }
  
  // Ensure max_val > min_val from precondition
  assert min_val <= max_val;
  assert forall j :: 0 <= j < |s| ==> min_val <= s[j] <= max_val;
  
  // From precondition: there exist distinct values
  assert exists i, j :: 0 <= i < j < |s| && s[i] != s[j];
  // This implies max_val > min_val
  assert max_val > min_val;
  
  // Create the result sequence
  r := [];
  i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == (s[j] - min_val) / (max_val - min_val)
    invariant forall j :: 0 <= j < i ==> 0.0 <= r[j] <= 1.0
  {
    var scaled := (s[i] - min_val) / (max_val - min_val);
    r := r + [scaled];
    i := i + 1;
  }
  
  // Verify postconditions
  assert r[min_idx] == (s[min_idx] - min_val) / (max_val - min_val) == 0.0;
  assert r[max_idx] == (s[max_idx] - min_val) / (max_val - min_val) == 1.0;
  
  affine_correctness(s, r, min_val, max_val);
}
// </vc-code>

