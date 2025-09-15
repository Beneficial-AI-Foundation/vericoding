// <vc-preamble>
function dist(a: real, b: real) : (d : real)
    ensures d >= 0.0
    ensures (d == 0.0) <==> a == b
{
    if a < b then b - a else a - b
}
function des(s: seq<real>, a: int, b: int) : bool {

    0 <= a < |s| && 0 <= b < |s| && a != b
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method find_closest_elements(s: seq<real>) returns (l : real, h : real)

    requires |s| >= 2

    ensures exists a, b : int :: des(s, a, b) && l == s[a] && h == s[b]
    ensures forall a, b : int :: des(s, a, b) ==> dist(l, h) <= dist(s[a], s[b])
    ensures l <= h
// </vc-spec>
// <vc-code>
{
  var closest_l: real := s[0];
  var closest_h: real := s[1];

  if s[0] > s[1] {
    closest_l := s[1];
    closest_h := s[0];
  }

  var i: int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant exists a, b :: des(s, a, b) && closest_l == s[a] && closest_h == s[b]
    invariant closest_l <= closest_h
    invariant forall a', b' :: 0 <= a' < i && 0 <= b' < i && a' != b' ==> dist(closest_l, closest_h) <= dist(s[a'], s[b'])

    invariant forall a', b' :: 0 <= a' < i && 0 <= b' < |s| && a' != b' ==> dist(closest_l, closest_h) <= dist(s[a'], s[b'])


  {
    var j: int := i + 1;
    while j < |s|
      invariant i < j <= |s|
      invariant 0 <= i < |s|
      invariant exists a, b :: des(s, a, b) && closest_l == s[a] && closest_h == s[b]
      invariant closest_l <= closest_h

      invariant forall a', b' :: 0 <= a' < i && 0 <= b' < |s| && a' != b' ==> dist(closest_l, closest_h) <= dist(s[a'], s[b'])
      invariant forall b' :: i < b' < j ==> dist(closest_l, closest_h) <= dist(s[i], s[b'])
    {
      if dist(s[i], s[j]) < dist(closest_l, closest_h) {
        if s[i] <= s[j] {
          closest_l := s[i];
          closest_h := s[j];
        } else {
          closest_l := s[j];
          closest_h := s[i];
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }

  l := closest_l;
  h := closest_h;
}
// </vc-code>
