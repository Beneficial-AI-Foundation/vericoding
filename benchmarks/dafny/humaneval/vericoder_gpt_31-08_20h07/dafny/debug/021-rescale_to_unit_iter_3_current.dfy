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
lemma DivBounds(a: real, d: real)
  requires d > 0.0
  requires 0.0 <= a <= d
  ensures 0.0 <= a/d <= 1.0
{
  // Upper bound
  assert a/d <= d/d;
  assert d/d == 1.0;
  // Lower bound
  assert 0.0 <= a/d;
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
  var n := |s|;
  var k := 1;
  var mindx:int := 0;
  var maxdx:int := 0;
  var minv: real := s[0];
  var maxv: real := s[0];

  while k < n
    invariant 1 <= k <= n
    invariant 0 <= mindx < k
    invariant 0 <= maxdx < k
    invariant minv == s[mindx]
    invariant maxv == s[maxdx]
    invariant forall t :: 0 <= t < k ==> s[mindx] <= s[t] <= s[maxdx]
  {
    var x := s[k];
    if x < minv {
      minv := x;
      mindx := k;
    }
    if x > maxv {
      maxv := x;
      maxdx := k;
    }
    k := k + 1;
  }

  ghost var i:int, j:int :| 0 <= i < j < n && s[i] != s[j];
  assert s[mindx] <= s[i];
  assert s[i] <= s[maxdx];
  assert s[mindx] <= s[j];
  assert s[j] <= s[maxdx];
  assert s[i] < s[j] || s[j] < s[i];
  if s[i] < s[j] {
    assert s[mindx] < s[maxdx];
  } else {
    assert s[j] < s[i];
    assert s[mindx] < s[maxdx];
  }

  var denom: real := maxv - minv;
  assert denom > 0.0;

  var t := 0;
  r := [];
  while t < n
    invariant 0 <= t <= n
    invariant |r| == t
    invariant forall u :: 0 <= u < t ==> r[u] == (s[u] - minv) / denom
  {
    r := r + [ (s[t] - minv) / denom ];
    t := t + 1;
  }

  assert |r| == n;
  assert forall t :: 0 <= t < n ==> r[t] == (s[t] - minv) / denom;

  assert 0 <= mindx < n && 0 <= maxdx < n;

  assert minv == s[mindx] && maxv == s[maxdx];

  assert r[mindx] == (s[mindx] - minv) / denom;
  assert s[mindx] - minv == 0.0;
  assert r[mindx] == 0.0;

  assert r[maxdx] == (s[maxdx] - minv) / denom;
  assert s[maxdx] - minv == denom;
  assert r[maxdx] == 1.0;

  assert forall t :: 0 <= t < n ==> minv <= s[t] <= maxv;
  assert forall t :: 0 <= t < n ==> 0.0 <= s[t] - minv <= denom;
  assert forall t :: 0 <= t < n ==> 0.0 <= (s[t] - minv) / denom <= 1.0
    by {
      assert denom > 0.0;
      assert 0.0 <= s[t] - minv <= denom;
      DivBounds(s[t] - minv, denom);
    }
  assert forall t :: 0 <= t < n ==> 0.0 <= r[t] <= 1.0;

  var shift: real := -minv;
  var scale: real := denom;
  assert scale > 0.0;
  assert |r| == |s|;
  assert forall t :: 0 <= t < n ==> r[t] == affine(s[t], shift, scale);
  assert affine_seq(s, r, shift, scale);
  assert exists shift2: real, scale2: real :: scale2 > 0.0 && affine_seq(s, r, shift2, scale2);
}
// </vc-code>

