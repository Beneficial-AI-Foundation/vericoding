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
/* helper modified by LLM (iteration 5): lemma proving affine rescaling keeps values in [0,1] given bounds and positive scale */
lemma affine_bounds(x: real, shift: real, scale: real, mn: real, mx: real)
  requires mn < mx
  requires shift == -mn
  requires scale == mx - mn
  requires mn <= x <= mx
  ensures 0.0 <= affine(x, shift, scale) <= 1.0
{
  assert scale > 0.0;
  assert affine(x, shift, scale) == (x + shift) / scale;
  assert affine(x, shift, scale) == (x - mn) / scale;
  assert 0.0 <= x - mn;
  assert x - mn <= mx - mn;
  assert 0.0 <= (x - mn) / scale;
  assert (x - mn) / scale <= (mx - mn) / scale;
  assert (mx - mn) / scale == 1.0;
}

/* helper modified by LLM (iteration 5): lemma establishing exact endpoint values after rescaling */
lemma affine_endpoints(shift: real, scale: real, mn: real, mx: real)
  requires mn < mx
  requires shift == -mn
  requires scale == mx - mn
  ensures affine(mn, shift, scale) == 0.0
  ensures affine(mx, shift, scale) == 1.0
{
  assert scale > 0.0;
  assert affine(mn, shift, scale) == (mn + shift) / scale;
  assert mn + shift == 0.0;
  assert (mn + shift) / scale == 0.0;

  assert affine(mx, shift, scale) == (mx + shift) / scale;
  assert mx + shift == mx - mn;
  assert (mx - mn) == scale;
  assert (mx - mn) / scale == scale / scale;
  assert scale / scale == 1.0;
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
  /* code modified by LLM (iteration 5): compute min/max, rescale affinely, prove bounds and endpoint equalities */
  var n := |s|;
  var mn := s[0];
  var mx := s[0];
  var minIdx := 0;
  var maxIdx := 0;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant 0 <= minIdx < i
    invariant 0 <= maxIdx < i
    invariant mn == s[minIdx]
    invariant mx == s[maxIdx]
    invariant forall k :: 0 <= k < i ==> s[minIdx] <= s[k] <= s[maxIdx]
    decreases n - i
  {
    if s[i] < mn {
      mn := s[i];
      minIdx := i;
    }
    if s[i] > mx {
      mx := s[i];
      maxIdx := i;
    }
    i := i + 1;
  }

  var p, q :| 0 <= p < q < n && s[p] != s[q];
  assert s[minIdx] <= s[p] <= s[maxIdx];
  assert s[minIdx] <= s[q] <= s[maxIdx];
  if s[p] < s[q] {
    assert s[minIdx] <= s[p] < s[q] <= s[maxIdx];
    assert mn < mx;
  } else {
    assert s[q] < s[p];
    assert s[minIdx] <= s[q] < s[p] <= s[maxIdx];
    assert mn < mx;
  }

  var shift := -mn;
  var scale := mx - mn;
  assert scale > 0.0;

  var tmp: seq<real> := [];
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant |tmp| == j
    invariant forall k :: 0 <= k < j ==> tmp[k] == affine(s[k], shift, scale)
    decreases n - j
  {
    tmp := tmp + [affine(s[j], shift, scale)];
    j := j + 1;
  }
  r := tmp;
  assert |r| == n;
  assert |r| == |s|;

  forall k | 0 <= k < n
    ensures r[k] == affine(s[k], shift, scale)
  {
    assert r[k] == tmp[k];
    assert tmp[k] == affine(s[k], shift, scale);
  }

  assert forall t :: 0 <= t < n ==> s[minIdx] <= s[t] <= s[maxIdx];
  forall t | 0 <= t < n
    ensures 0.0 <= r[t] <= 1.0
  {
    assert s[minIdx] <= s[t] <= s[maxIdx];
    affine_bounds(s[t], shift, scale, mn, mx);
    assert r[t] == affine(s[t], shift, scale);
  }

  assert 0 <= minIdx < n && 0 <= maxIdx < n;
  assert s[minIdx] == mn && s[maxIdx] == mx;
  affine_endpoints(shift, scale, mn, mx);
  assert r[minIdx] == affine(s[minIdx], shift, scale);
  assert r[minIdx] == affine(mn, shift, scale);
  assert r[minIdx] == 0.0;
  assert r[maxIdx] == affine(s[maxIdx], shift, scale);
  assert r[maxIdx] == affine(mx, shift, scale);
  assert r[maxIdx] == 1.0;

  assert scale > 0.0;
  assert affine_seq(s, r, shift, scale);
}
// </vc-code>
