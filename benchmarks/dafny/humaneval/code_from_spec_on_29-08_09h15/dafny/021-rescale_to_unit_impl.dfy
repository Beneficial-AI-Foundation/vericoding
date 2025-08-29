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
function min_seq(s: seq<real>) : real
  requires |s| >= 1
{
  if |s| == 1 then s[0]
  else if s[0] <= min_seq(s[1..]) then s[0]
  else min_seq(s[1..])
}

function max_seq(s: seq<real>) : real
  requires |s| >= 1
{
  if |s| == 1 then s[0]
  else if s[0] >= max_seq(s[1..]) then s[0]
  else max_seq(s[1..])
}

lemma min_seq_properties(s: seq<real>)
  requires |s| >= 1
  ensures forall i :: 0 <= i < |s| ==> min_seq(s) <= s[i]
  ensures exists i :: 0 <= i < |s| && min_seq(s) == s[i]
{
  if |s| == 1 {
    assert min_seq(s) == s[0];
    assert exists i :: 0 <= i < |s| && min_seq(s) == s[i];
  } else {
    min_seq_properties(s[1..]);
    if s[0] <= min_seq(s[1..]) {
      assert min_seq(s) == s[0];
      assert exists i :: 0 <= i < |s| && min_seq(s) == s[i];
    } else {
      var j :| 0 <= j < |s[1..]| && min_seq(s[1..]) == s[1..][j];
      assert s[1..][j] == s[j+1];
      assert exists i :: 0 <= i < |s| && min_seq(s) == s[i];
    }
  }
}

lemma max_seq_properties(s: seq<real>)
  requires |s| >= 1
  ensures forall i :: 0 <= i < |s| ==> s[i] <= max_seq(s)
  ensures exists i :: 0 <= i < |s| && max_seq(s) == s[i]
{
  if |s| == 1 {
    assert max_seq(s) == s[0];
    assert exists i :: 0 <= i < |s| && max_seq(s) == s[i];
  } else {
    max_seq_properties(s[1..]);
    if s[0] >= max_seq(s[1..]) {
      assert max_seq(s) == s[0];
      assert exists i :: 0 <= i < |s| && max_seq(s) == s[i];
    } else {
      var j :| 0 <= j < |s[1..]| && max_seq(s[1..]) == s[1..][j];
      assert s[1..][j] == s[j+1];
      assert exists i :: 0 <= i < |s| && max_seq(s) == s[i];
    }
  }
}

lemma affine_preserves_order(x: real, y: real, shift: real, scale: real)
  requires scale > 0.0
  requires x <= y
  ensures affine(x, shift, scale) <= affine(y, shift, scale)
{
}

lemma affine_maps_min_max(s: seq<real>, shift: real, scale: real)
  requires |s| >= 1
  requires scale > 0.0
  ensures affine(min_seq(s), shift, scale) == min_seq(seq(|s|, i requires 0 <= i < |s| => affine(s[i], shift, scale)))
  ensures affine(max_seq(s), shift, scale) == max_seq(seq(|s|, i requires 0 <= i < |s| => affine(s[i], shift, scale)))
{
  var transformed := seq(|s|, i requires 0 <= i < |s| => affine(s[i], shift, scale));
  min_seq_properties(s);
  max_seq_properties(s);
  min_seq_properties(transformed);
  max_seq_properties(transformed);
  
  forall i | 0 <= i < |s|
    ensures min_seq(s) <= s[i]
    ensures s[i] <= max_seq(s)
    ensures affine(min_seq(s), shift, scale) <= transformed[i]
    ensures transformed[i] <= affine(max_seq(s), shift, scale)
  {
    affine_preserves_order(min_seq(s), s[i], shift, scale);
    affine_preserves_order(s[i], max_seq(s), shift, scale);
  }
  
  var min_idx :| 0 <= min_idx < |s| && s[min_idx] == min_seq(s);
  var max_idx :| 0 <= max_idx < |s| && s[max_idx] == max_seq(s);
  
  assert transformed[min_idx] == affine(s[min_idx], shift, scale) == affine(min_seq(s), shift, scale);
  assert transformed[max_idx] == affine(s[max_idx], shift, scale) == affine(max_seq(s), shift, scale);
}

lemma division_properties(a: real, b: real)
  requires b > 0.0
  ensures (a / b) / (b / b) == a / b
  ensures b / b == 1.0
{
}

lemma division_bounds(x: real, min_val: real, max_val: real, scale: real)
  requires scale == max_val - min_val
  requires scale > 0.0
  requires min_val <= x <= max_val
  ensures 0.0 <= (x - min_val) / scale <= 1.0
{
  assert 0.0 <= x - min_val <= max_val - min_val;
  assert x - min_val <= scale;
  assert (x - min_val) / scale <= scale / scale;
  division_properties(scale, scale);
  assert (x - min_val) / scale <= 1.0;
  assert 0.0 <= x - min_val;
  assert 0.0 / scale <= (x - min_val) / scale;
  assert 0.0 <= (x - min_val) / scale;
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def rescale_to_unit(numbers: List[float]) -> List[float]
Given list of numbers (of at least two elements), apply a linear transform to that list, such that the smallest number will become 0 and the largest will become 1
*/
// </vc-description>

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
  min_seq_properties(s);
  max_seq_properties(s);
  
  var min_val := min_seq(s);
  var max_val := max_seq(s);
  
  var shift := -min_val;
  var scale := max_val - min_val;
  
  assert scale > 0.0 by {
    min_seq_properties(s);
    max_seq_properties(s);
    assert exists i, j :: 0 <= i < j < |s| && s[i] != s[j];
    assert min_val <= max_val;
    assert min_val != max_val;
    assert scale > 0.0;
  }
  
  r := seq(|s|, i requires 0 <= i < |s| => affine(s[i], shift, scale));
  
  assert affine_seq(s, r, shift, scale) by {
    forall i | 0 <= i < |s|
      ensures r[i] == affine(s[i], shift, scale)
    {
    }
  }
  
  assert exists i :: 0 <= i < |s| && r[i] == 0.0 by {
    min_seq_properties(s);
    var min_idx :| 0 <= min_idx < |s| && s[min_idx] == min_val;
    assert r[min_idx] == affine(s[min_idx], shift, scale);
    assert r[min_idx] == affine(min_val, -min_val, scale);
    assert r[min_idx] == (min_val - min_val) / scale;
    assert r[min_idx] == 0.0 / scale;
    assert r[min_idx] == 0.0;
  }
  
  assert exists i :: 0 <= i < |s| && r[i] == 1.0 by {
    max_seq_properties(s);
    var max_idx :| 0 <= max_idx < |s| && s[max_idx] == max_val;
    assert r[max_idx] == affine(s[max_idx], shift, scale);
    assert r[max_idx] == affine(max_val, -min_val, scale);
    assert r[max_idx] == (max_val - min_val) / scale;
    assert r[max_idx] == scale / scale;
    division_properties(scale, scale);
    assert r[max_idx] == 1.0;
  }
  
  assert forall i :: 0 <= i < |s| ==> 0.0 <= r[i] <= 1.0 by {
    forall i | 0 <= i < |s|
      ensures 0.0 <= r[i] <= 1.0
    {
      min_seq_properties(s);
      max_seq_properties(s);
      assert r[i] == (s[i] + shift) / scale;
      assert r[i] == (s[i] - min_val) / scale;
      division_bounds(s[i], min_val, max_val, scale);
      assert 0.0 <= r[i] <= 1.0;
    }
  }
}
// </vc-code>

