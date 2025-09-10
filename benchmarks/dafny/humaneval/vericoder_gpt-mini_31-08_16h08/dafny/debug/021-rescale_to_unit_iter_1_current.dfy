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
lemma minmax_pos_from_range(s: seq<real>, lo: real, hi: real)
  requires |s| >= 2
  requires forall k :: 0 <= k < |s| ==> lo <= s[k] <= hi
  requires exists i, j :: 0 <= i < j < |s| && s[i] != s[j]
  ensures hi - lo > 0.0
{
  if hi <= lo {
    // If hi <= lo then for all k, s[k] == lo
    assert forall k :: 0 <= k < |s| ==> s[k] == lo by {
      calc {
        forall k :: 0 <= k < |s|
          {
            lo <= s[k] <= hi;
            <=>
            lo <= s[k] <= lo;
            <=>
            s[k] == lo;
          }
      }
    }
    // This contradicts the existence of two different elements
    assert false;
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
  var n := |s|;
  var a := new real[n];
  var lo := s[0];
  var hi := s[0];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant forall k :: 0 <= k < i ==> lo <= s[k] <= hi
    invariant exists p :: 0 <= p < i && s[p] == lo
    invariant exists q :: 0 <= q < i && s[q] == hi
  {
    if s[i] < lo { lo := s[i]; }
    if s[i] > hi { hi := s[i]; }
    i := i + 1;
  }

  // Ensure scale positive (uses precondition indirectly via lemma)
  var scale := hi - lo;
  minmax_pos_from_range(s, lo, hi);
  assert scale > 0.0;

  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> a[k] == (s[k] - lo) / scale
  {
    a[i] := (s[i] - lo) / scale;
    i := i + 1;
  }

  r := a[..];

  // Provide witnesses for the existential affine relation
  ghost var shift := -lo;
  ghost var sc := scale;
  assert sc > 0.0;
  assert forall k :: 0 <= k < n ==> r[k] == affine(s[k], shift, sc);

  assert exists sh, sc0 :: sc0 > 0.0 && affine_seq(s, r, sh, sc0) by {
    // witness
    reveal affine_seq;
    assert affine_seq(s, r, shift, sc);
    assert (exists sh, sc0 :: sh == shift && sc0 == sc && sc0 > 0.0 && affine_seq(s, r, sh, sc0));
  }

  // Existence of 0.0 and 1.0 in r
  assert exists i0 :: 0 <= i0 < n && r[i0] == 0.0 by {
    // from invariants at loop end we know some index had s[index] == lo
    assert exists p :: 0 <= p < n && s[p] == lo;
    // pick that p; r[p] == (s[p]-lo)/scale == 0
    assert forall k :: 0 <= k < n ==> (s[k] == lo) ==> r[k] == 0.0;
    assert (exists p :: 0 <= p < n && r[p] == 0.0);
  }

  assert exists i1 :: 0 <= i1 < n && r[i1] == 1.0 by {
    assert exists q :: 0 <= q < n && s[q] == hi;
    assert forall k :: 0 <= k < n ==> (s[k] == hi) ==> r[k] == 1.0;
    assert (exists q :: 0 <= q < n && r[q] == 1.0);
  }
}
// </vc-code>

