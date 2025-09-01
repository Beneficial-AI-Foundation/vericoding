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
lemma affine_properties(x: real, shift: real, scale: real)
  requires scale > 0.0
  ensures 0.0 <= affine(x, shift, scale) <= 1.0 ==>
          shift <= -x <= shift + scale
{
}

lemma shift_scale_exists(minVal: real, maxVal: real, x: real)
  requires minVal <= x <= maxVal
  requires minVal != maxVal
  ensures exists shift: real, scale: real ::
    scale > 0.0 && 0.0 <= affine(x, shift, scale) <= 1.0
{
  var shift := -minVal;
  var scale := maxVal - minVal;
  assert scale > 0.0;
  assert affine(x, shift, scale) == (x - minVal) / scale;
  assert 0.0 <= (x - minVal) / scale <= 1.0;
}

lemma min_max_invariant(s: seq<real>, i: int, minVal: real, maxVal: real)
  requires 0 <= i <= |s|
  requires forall j :: 0 <= j < i ==> minVal <= s[j] <= maxVal
  ensures forall j :: 0 <= j < i ==> minVal <= s[j] <= maxVal
{
}

lemma affine_range(minVal: real, maxVal: real, x: real)
  requires minVal != maxVal
  requires minVal <= x <= maxVal
  ensures 0.0 <= affine(x, -minVal, maxVal - minVal) <= 1.0
{
  assert maxVal - minVal > 0.0;
  var result := (x - minVal) / (maxVal - minVal);
  assert result >= 0.0;
  assert result <= 1.0;
}

lemma min_val_contained(s: seq<real>, i: int, minVal: real)
  requires 0 <= i <= |s|
  requires exists k :: 0 <= k < i && s[k] == minVal
  requires forall j :: 0 <= j < i ==> minVal <= s[j]
  ensures minVal in s[0..i]
{
}

lemma max_val_contained(s: seq<real>, i: int, maxVal: real)
  requires 0 <= i <= |s|
  requires exists k :: 0 <= k < i && s[k] == maxVal
  requires forall j :: 0 <= j < i ==> s[j] <= maxVal
  ensures maxVal in s[0..i]
{
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
  var minVal := s[0];
  var maxVal := s[0];
  var i := 1;
  
  while i < |s|
    invariant 1 <= i <= |s|
    invariant minVal in s[0..i]
    invariant maxVal in s[0..i]
    invariant forall j :: 0 <= j < i ==> minVal <= s[j] <= maxVal
  {
    if s[i] < minVal {
      minVal := s[i];
    }
    if s[i] > maxVal {
      maxVal := s[i];
    }
    i := i + 1;
  }
  
  assert minVal != maxVal;
  assert maxVal - minVal > 0.0;
  
  var shift := -minVal;
  var scale := maxVal - minVal;
  
  r := [];
  i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == affine(s[j], shift, scale)
    invariant forall j :: 0 <= j < i ==> 0.0 <= r[j] <= 1.0
  {
    affine_range(minVal, maxVal, s[i]);
    r := r + [affine(s[i], shift, scale)];
    i := i + 1;
  }
  
  var minIndex := 0;
  var maxIndex := 0;
  var j := 0;
  while j < |s|
    invariant 0 <= j <= |s|
    invariant exists k :: 0 <= k < j && s[k] == minVal ==> minIndex in [0..j) && s[minIndex] == minVal
    invariant exists k :: 0 <= k < j && s[k] == maxVal ==> maxIndex in [0..j) && s[maxIndex] == maxVal
  {
    if s[j] == minVal {
      minIndex := j;
    }
    if s[j] == maxVal {
      maxIndex := j;
    }
    j := j + 1;
  }
  
  assert r[minIndex] == affine(minVal, shift, scale) == (minVal - minVal) / scale == 0.0;
  assert r[maxIndex] == affine(maxVal, shift, scale) == (maxVal - minVal) / scale == 1.0;
}
// </vc-code>

