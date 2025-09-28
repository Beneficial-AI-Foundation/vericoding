// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added division lemma for non-linear arithmetic */
lemma DivLeOne(a: real, b: real)
  requires b > 0.0
  requires a <= b
  ensures a / b <= 1.0
{}

/* helper modified by LLM (iteration 3): strengthened proof using DivLeOne lemma */
lemma AffineBounds(x: real, min_val: real, max_val: real)
  requires min_val < max_val
  requires min_val <= x <= max_val
  ensures 0.0 <= affine(x, -min_val, max_val - min_val) <= 1.0
{
  var scale := max_val - min_val;
  assert scale > 0.0;
  var shift := -min_val;
  var res := affine(x, shift, scale);

  assert res == (x - min_val) / scale;

  // Prove lower bound
  assert 0.0 <= x - min_val;
  assert 0.0 <= res;

  // Prove upper bound
  assert x - min_val <= scale;
  DivLeOne(x - min_val, scale);
  assert res <= 1.0;
}
// </vc-helpers>

// <vc-spec>
method rescale_to_unit(s: seq<real>) returns (r : seq<real>)

  requires |s| >= 2
  requires exists i, j : int :: (0 <= i < j < |s|) && s[i] != s[j]

  ensures |r| == |s|
  ensures forall i : int :: 0 <= i < |s| ==> 0.0 <= r[i] <= 1.0
  ensures exists i : int :: 0 <= i < |s| && r[i] == 0.0
  ensures exists i : int :: 0 <= i < |s| && r[i] == 1.0
  ensures exists shift, scale :: scale > 0.0 && affine_seq(s, r, shift, scale)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): fix is in helpers, no changes to code body */
  // Find min and max values, and an index for each, in one pass.
  var min_s := s[0];
  var max_s := s[0];
  var min_idx := 0;
  var max_idx := 0;
  var i := 1;
  while i < |s|
    invariant 1 <= i <= |s|
    invariant 0 <= min_idx < i && s[min_idx] == min_s
    invariant 0 <= max_idx < i && s[max_idx] == max_s
    invariant forall j :: 0 <= j < i ==> min_s <= s[j] && s[j] <= max_s
  {
    if s[i] < min_s {
      min_s := s[i];
      min_idx := i;
    }
    if s[i] > max_s {
      max_s := s[i];
      max_idx := i;
    }
    i := i + 1;
  }

  // From the precondition, we know not all elements are equal, so min < max.
  if min_s == max_s {
    forall k | 0 <= k < |s| ensures s[k] == min_s {
      assert min_s <= s[k] <= max_s;
    }
    assert forall i, j :: 0 <= i < j < |s| ==> s[i] == s[j];
    assert false; // Contradicts `requires`
  }
  assert min_s < max_s;

  var shift := -min_s;
  var scale := max_s - min_s;
  assert scale > 0.0;

  // Compute the rescaled sequence using an intermediate array.
  var a := new real[|s|];
  var k := 0;
  while k < |s|
    invariant 0 <= k <= |s|
    invariant forall j :: 0 <= j < k ==> 0.0 <= a[j] <= 1.0
    invariant forall j :: 0 <= j < k ==> a[j] == affine(s[j], shift, scale)
  {
    assert min_s <= s[k] <= max_s;
    AffineBounds(s[k], min_s, max_s);
    a[k] := affine(s[k], shift, scale);
    assert 0.0 <= a[k] <= 1.0;
    k := k + 1;
  }

  r := a[..];

  // Prove postconditions.
  assert affine_seq(s, r, shift, scale) by {
    forall j | 0 <= j < |s|
      ensures r[j] == affine(s[j], shift, scale)
    {}
  }
  assert exists shift_p, scale_p :: scale_p > 0.0 && affine_seq(s, r, shift_p, scale_p);
  
  assert s[min_idx] == min_s;
  assert r[min_idx] == affine(s[min_idx], shift, scale) == 0.0;
  assert exists j :: 0 <= j < |s| && r[j] == 0.0;

  assert s[max_idx] == max_s;
  assert r[max_idx] == affine(s[max_idx], shift, scale) == 1.0;
  assert exists j :: 0 <= j < |s| && r[j] == 1.0;
}
// </vc-code>
