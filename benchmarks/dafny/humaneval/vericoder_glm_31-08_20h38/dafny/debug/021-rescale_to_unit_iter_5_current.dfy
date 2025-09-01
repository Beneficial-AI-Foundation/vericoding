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
    for i := 1 to |s|
        invariant min_val <= max_val
        invariant forall j :: 0 <= j < i ==> min_val <= s[j] <= max_val
        invariant exists j :: 0 <= j < i && s[j] == min_val
        invariant exists j :: 0 <= j < i && s[j] == max_val
    {
        if s[i] < min_val {
            min_val := s[i];
        } else if s[i] > max_val {
            max_val := s[i];
        }
    }

    assert min_val < max_val;
    var shift := -min_val;
    var scale := max_val - min_val;
    assert scale > 0.0;

    var arr := new real[|s|];
    for i := 0 to |s|-1
        invariant forall j :: 0 <= j < i ==> arr[j] == affine(s[j], -min_val, scale)
        invariant forall j :: 0 <= j < i ==> 0.0 <= arr[j] <= 1.0
    {
        arr[i] := (s[i] - min_val) / scale;
    }

    r := arr[..];

    ghost var i0 : int :| 0 <= i0 < |s| && s[i0] == min_val;
    ghost var i1 : int :| 0 <= i1 < |s| && s[i1] == max_val;
    assert r[i0] == 0.0;
    assert r[i1] == 1.0;

    assert affine_seq(s, r, -min_val, scale);

    return r;
}
// </vc-code>

