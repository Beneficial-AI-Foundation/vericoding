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
  var min_s := s[0];
  var max_s := s[0];
  var minIndex := 0;
  var maxIndex := 0;
  for i := 1 to |s|
    invariant 0 <= i <= |s|
    invariant 0 <= minIndex < i
    invariant 0 <= maxIndex < i
    invariant s[minIndex] == min_s
    invariant s[maxIndex] == max_s
    invariant forall j :: 0 <= j < i ==> min_s <= s[j] <= max_s
  {
    if s[i] < min_s {
      min_s := s[i];
      minIndex := i;
    } else if s[i] > max_s {
      max_s := s[i];
      maxIndex := i;
    }
  }
  var scale := max_s - min_s;
  var shift := -min_s;
  r := [];
  for i := 0 to |s|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == (s[j] + shift) / scale
  {
    r := r + [(s[i] + shift) / scale];
  }
  assert s[minIndex] == min_s && s[maxIndex] == max_s;
  assert scale > 0.0;
  assert r[minIndex] == 0.0;
  assert r[maxIndex] == 1.0;
  assert affine_seq(s, r, shift, scale);
  return r;
}
// </vc-code>

