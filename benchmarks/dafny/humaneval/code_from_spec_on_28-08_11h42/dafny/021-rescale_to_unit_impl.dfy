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
lemma MinMaxExists(s: seq<real>)
  requires |s| >= 1
  ensures exists i :: 0 <= i < |s| && forall j :: 0 <= j < |s| ==> s[i] <= s[j]
  ensures exists i :: 0 <= i < |s| && forall j :: 0 <= j < |s| ==> s[j] <= s[i]
{
  var min_idx := 0;
  var max_idx := 0;
  
  for k := 1 to |s|
    invariant 0 <= min_idx < |s|
    invariant 0 <= max_idx < |s|
    invariant forall j :: 0 <= j < k ==> s[min_idx] <= s[j]
    invariant forall j :: 0 <= j < k ==> s[j] <= s[max_idx]
  {
    if s[k] < s[min_idx] {
      min_idx := k;
    }
    if s[k] > s[max_idx] {
      max_idx := k;
    }
  }
}

lemma AffinePreservesOrder(x: real, y: real, shift: real, scale: real)
  requires scale > 0.0
  requires x <= y
  ensures affine(x, shift, scale) <= affine(y, shift, scale)
{
}

lemma AffineRangeProperty(s: seq<real>, min_val: real, max_val: real, shift: real, scale: real)
  requires scale > 0.0
  requires forall i :: 0 <= i < |s| ==> min_val <= s[i] <= max_val
  ensures forall i :: 0 <= i < |s| ==> affine(min_val, shift, scale) <= affine(s[i], shift, scale) <= affine(max_val, shift, scale)
{
  forall i | 0 <= i < |s|
    ensures affine(min_val, shift, scale) <= affine(s[i], shift, scale) <= affine(max_val, shift, scale)
  {
    AffinePreservesOrder(min_val, s[i], shift, scale);
    AffinePreservesOrder(s[i], max_val, shift, scale);
  }
}

lemma AffineEndpointValues(min_val: real, max_val: real, shift: real, scale: real)
  requires scale > 0.0
  requires shift == -min_val
  requires scale == max_val - min_val
  requires min_val < max_val
  ensures affine(min_val, shift, scale) == 0.0
  ensures affine(max_val, shift, scale) == 1.0
{
  assert affine(min_val, shift, scale) == (min_val + (-min_val)) / (max_val - min_val) == 0.0 / (max_val - min_val) == 0.0;
  calc {
    affine(max_val, shift, scale);
    == { assert shift == -min_val; assert scale == max_val - min_val; }
      (max_val + shift) / scale;
    == { assert shift == -min_val; }
      (max_val + (-min_val)) / scale;
    == { assert scale == max_val - min_val; }
      (max_val - min_val) / (max_val - min_val);
    == { assert max_val - min_val != 0.0; }
      1.0;
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
  MinMaxExists(s);
  
  var min_val := s[0];
  var max_val := s[0];
  var min_idx := 0;
  var max_idx := 0;
  
  for i := 1 to |s|
    invariant forall j :: 0 <= j < i ==> min_val <= s[j]
    invariant forall j :: 0 <= j < i ==> s[j] <= max_val
    invariant 0 <= min_idx < |s| && s[min_idx] == min_val
    invariant 0 <= max_idx < |s| && s[max_idx] == max_val
    invariant exists k :: 0 <= k < i && s[k] == min_val
    invariant exists k :: 0 <= k < i && s[k] == max_val
  {
    if s[i] < min_val {
      min_val := s[i];
      min_idx := i;
    }
    if s[i] > max_val {
      max_val := s[i];
      max_idx := i;
    }
  }
  
  assert forall j :: 0 <= j < |s| ==> min_val <= s[j] <= max_val;
  assert min_val < max_val;
  
  var shift := -min_val;
  var scale := max_val - min_val;
  
  AffineEndpointValues(min_val, max_val, shift, scale);
  
  r := [];
  for i := 0 to |s|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == affine(s[j], shift, scale)
    invariant forall j :: 0 <= j < i ==> 0.0 <= r[j] <= 1.0
  {
    var transformed := affine(s[i], shift, scale);
    assert 0.0 <= transformed <= 1.0 by {
      AffinePreservesOrder(min_val, s[i], shift, scale);
      AffinePreservesOrder(s[i], max_val, shift, scale);
      assert affine(min_val, shift, scale) == 0.0;
      assert affine(max_val, shift, scale) == 1.0;
    }
    r := r + [transformed];
  }
  
  assert r[min_idx] == affine(min_val, shift, scale) == 0.0;
  assert r[max_idx] == affine(max_val, shift, scale) == 1.0;
  assert affine_seq(s, r, shift, scale);
}
// </vc-code>
