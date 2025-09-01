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
function min_real_seq(s: seq<real>): real
  requires |s| > 0
  ensures forall i :: 0 <= i < |s| ==> s[i] >= min_real_seq(s)
  ensures exists i :: 0 <= i < |s| && s[i] == min_real_seq(s)
{
  if |s| == 1 then s[0]
  else if s[0] < min_real_seq(s[1..]) then s[0]
  else min_real_seq(s[1..])
}

function max_real_seq(s: seq<real>): real
  requires |s| > 0
  ensures forall i :: 0 <= i < |s| ==> s[i] <= max_real_seq(s)
  ensures exists i :: 0 <= i < |s| && s[i] == max_real_seq(s)
{
  if |s| == 1 then s[0]
  else if s[0] > max_real_seq(s[1..]) then s[0]
  else max_real_seq(s[1..])
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
    var min_s := min_real_seq(s);
    var max_s := max_real_seq(s);

    var shift := -min_s;
    var scale := max_s - min_s;

    // The requires clause `exists i, j : int :: (0 <= i < j < |s|) && s[i] != s[j]` 
    // combined with the definition of min_real_seq and max_real_seq 
    // implies that max_s != min_s, so scale > 0.0.
    // We need to prove this explicitly for Dafny.
    if scale == 0.0 {
      // This branch implies min_s == max_s, which means all elements in s are equal.
      // This contradicts the precondition `exists i, j : int :: (0 <= i < j < |s|) && s[i] != s[j]`.
      // So, this branch is unreachable.
      assert false;
    }

    r := new real[|s|];
    for i := 0 to |s| - 1
        invariant 0 <= i <= |s|
        invariant |r| == |s|
        invariant forall k :: 0 <= k < i ==> r[k] == affine(s[k], shift, scale)
        invariant forall k :: 0 <= k < i ==> 0.0 <= r[k] <= 1.0
    {
        r[i] := affine(s[i], shift, scale);
    }
}
// </vc-code>

