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
lemma min_max_properties(s: seq<real>, min_val: real, max_val: real)
  requires |s| >= 1
  requires forall i :: 0 <= i < |s| ==> min_val <= s[i] <= max_val
  requires exists i :: 0 <= i < |s| && s[i] == min_val
  requires exists j :: 0 <= j < |s| && s[j] == max_val
  requires min_val < max_val
  ensures max_val - min_val > 0.0
  ensures forall i :: 0 <= i < |s| ==> 0.0 <= (s[i] - min_val) / (max_val - min_val) <= 1.0
  ensures exists i :: 0 <= i < |s| && (s[i] - min_val) / (max_val - min_val) == 0.0
  ensures exists j :: 0 <= j < |s| && (s[j] - min_val) / (max_val - min_val) == 1.0
{
}

lemma affine_transformation_lemma(s: seq<real>, r: seq<real>, min_val: real, max_val: real)
  requires |s| == |r|
  requires min_val < max_val
  requires forall i :: 0 <= i < |s| ==> r[i] == (s[i] - min_val) / (max_val - min_val)
  ensures affine_seq(s, r, -min_val, max_val - min_val)
{
  assert max_val - min_val > 0.0;
  forall i | 0 <= i < |s|
    ensures r[i] == affine(s[i], -min_val, max_val - min_val)
  {
    calc {
      affine(s[i], -min_val, max_val - min_val);
      (s[i] + (-min_val)) / (max_val - min_val);
      (s[i] - min_val) / (max_val - min_val);
      r[i];
    }
  }
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
  var min_val := s[0];
  var max_val := s[0];
  var min_idx := 0;
  var max_idx := 0;
  
  var i := 1;
  while i < |s|
    invariant 1 <= i <= |s|
    invariant 0 <= min_idx < i && 0 <= max_idx < i
    invariant min_val == s[min_idx] && max_val == s[max_idx]
    invariant forall j :: 0 <= j < i ==> min_val <= s[j] <= max_val
  {
    if s[i] < min_val {
      min_val := s[i];
      min_idx := i;
    }
    if s[i] > max_val {
      max_val := s[i];
      max_idx := i;
    }
    i := i + 1;
  }
  
  assert forall j :: 0 <= j < |s| ==> min_val <= s[j] <= max_val;
  assert s[min_idx] == min_val;
  assert s[max_idx] == max_val;
  assert 0 <= min_idx < |s| && 0 <= max_idx < |s|;
  assert exists idx :: 0 <= idx < |s| && s[idx] == min_val by { assert s[min_idx] == min_val; }
  assert exists idx :: 0 <= idx < |s| && s[idx] == max_val by { assert s[max_idx] == max_val; }
  assert min_val < max_val;
  
  r := [];
  i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == (s[j] - min_val) / (max_val - min_val)
  {
    r := r + [(s[i] - min_val) / (max_val - min_val)];
    i := i + 1;
  }
  
  min_max_properties(s, min_val, max_val);
  affine_transformation_lemma(s, r, min_val, max_val);
}
// </vc-code>

