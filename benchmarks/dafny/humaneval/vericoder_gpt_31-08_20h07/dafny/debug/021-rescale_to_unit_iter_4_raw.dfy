```vc-helpers
lemma DivBounds(a: real, d: real)
  requires d > 0.0
  requires 0.0 <= a <= d
  ensures 0.0 <= a/d <= 1.0
{
  // Lower bound
  assert 0.0 <= a;
  assert 0.0/d == 0.0;
  assert 0.0 <= a/d;

  // Upper bound
  assert a <= d;
  assert a/d <= d/d;
  assert d/d == 1.0;
}
```

```vc-code
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

  assert forall t :: 0 <= t < n ==> minv <= s[t] <= maxv
    by {
      assume 0 <= t < n;
      // From the loop invariant at exit (k == n)
      assert forall u :: 0 <= u < n ==> s[mindx] <= s[u] <= s[maxdx];
      assert s[mindx] <= s[t] <= s[maxdx];
      assert minv == s[mindx] && maxv == s[maxdx];
    }

  assert forall t :: 0 <= t < n ==> 0.0 <= (s[t] - minv) / denom <= 1.0
    by {
      assume 0 <= t < n;
      assert minv <= s[t] <= maxv;
      assert 0.0 <= s[t] - minv;
      assert s[t] - minv <= maxv - minv;
      assert denom == maxv - minv;
      assert s[t] - minv <= denom;
      assert denom > 0.0;
      DivBounds(s[t] - minv, denom);
    }
  assert forall t :: 0 <= t < n ==> 0.0 <= r[t] <= 1.0
    by {
      assume 0 <= t < n;
      assert r[t] == (s[t] - minv) / denom;
      assert 0.0 <= (s[t] - minv) / denom <= 1.0;
    }

  var shift: real := -minv;
  var scale: real := denom;
  assert scale > 0.0;
  assert |r| == |s|;
  assert forall t :: 0 <= t < n ==> r[t] == affine(s[t], shift, scale)
    by {
      assume 0 <= t < n;
      assert r[t] == (s[t] - minv) / denom;
      assert scale == denom;
      assert s[t] + shift == s[t] - minv;
    }
  assert affine_seq(s, r, shift, scale);
}
```