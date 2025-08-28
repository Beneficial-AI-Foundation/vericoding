function affine(x: real, shift: real, scale: real) : real
    requires scale > 0.0
{
    (x + shift) / scale
}
// pure-end
lemma affine_zero(x: real, shift: real, scale: real)
    requires x == -shift
    requires scale > 0.0
    ensures affine(x, shift, scale) == 0.0 {}
// pure-end
lemma affine_unit(x: real, shift: real, scale: real)
    requires x == scale - shift
    requires scale > 0.0
    ensures affine(x, shift, scale) == 1.0 {}
// pure-end

function affine_seq(s: seq<real>, r: seq<real>, shift: real, scale: real) : bool
  requires scale > 0.0
  requires |r| == |s|
{
  forall i :: 0 <= i < |s| ==> r[i] == affine(s[i], shift, scale)
}
// pure-end

lemma div_unit(x: real, scale: real)
    requires 0.0 <= x <= scale
    requires scale > 0.0
    ensures x / scale <= 1.0 {}
// pure-end
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
{
    // impl-start
    var mni : int := if s[0] < s[1] then 0 else 1;
    var mxi : int := if s[0] < s[1] then 1 else 0;
    for i := 2 to |s|
        // invariants-start
        invariant 0 <= mni < |s|
        invariant 0 <= mxi < |s|
        invariant forall j : int :: (0 <= j < i) ==> s[mni] <= s[j] <= s[mxi]
        invariant s[mni] <= s[mxi]
        // invariants-end
    {
        if (s[i] < s[mni]) {
            mni := i;
        }
        if (s[i] > s[mxi]) {
            mxi := i;
        }
    }
    var shift := -s[mni];
    var scale := s[mxi] - s[mni];
    assert scale > 0.0; // assert-line
    r := [];
    for j := 0 to |s|
        // invariants-start
        invariant |r| == j
        invariant forall k : int :: 0 <= k < j ==> 0.0 <= r[k] <= 1.0
        invariant affine_seq(s[..j], r, shift, scale)
        // invariants-end
    {
        var rj : real := affine(s[j], shift, scale);
        // assert-start
        assert rj <= 1.0 by {
            div_unit(s[j] + shift, scale);
        }
        // assert-end
        r := r + [rj];
    }
    assert s[..|s|] == s; // assert-line
    // assert-start
    assert r[mni] == 0.0 by {
        affine_zero(s[mni], shift, scale);
    }
    // assert-end
    // assert-start
    assert r[mxi] == 1.0 by {
        affine_unit(s[mxi], shift, scale);
    }
    // assert-end
    // impl-end
}
