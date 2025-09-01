function dist(a: real, b: real) : (d : real)
    ensures d >= 0.0
    ensures (d == 0.0) <==> a == b
{
    if a < b then b - a else a - b
}
function des(s: seq<real>, a: int, b: int) : bool {
    // distinct elements
    0 <= a < |s| && 0 <= b < |s| && a != b
}

// <vc-helpers>
lemma {:induction false} MinDistProperties(s: seq<real>, i: int, j: int, min_i: int, min_j: int)
  requires |s| >= 2
  requires 0 <= i <= |s|
  requires 0 <= j <= |s|
  requires 0 <= min_i < |s|
  requires 0 <= min_j < |s|
  requires min_i != min_j
  requires forall a, b: int :: 0 <= a < i && 0 <= b < |s| && a != b ==> dist(s[min_i], s[min_j]) <= dist(s[a], s[b])
  requires forall a, b: int :: 0 <= a < j && a != j ==> dist(s[min_i], s[min_j]) <= dist(s[a], s[j])
  ensures forall a, b: int :: 0 <= a <= i && 0 <= b <= j && a != b ==> dist(s[min_i], s[min_j]) <= dist(s[a], s[b])
{
}

lemma PairExists(s: seq<real>)
  requires |s| >= 2
  ensures exists a, b: int :: des(s, a, b)
{
}
// </vc-helpers>

// <vc-spec>
method find_closest_elements(s: seq<real>) returns (l : real, h : real)
    // pre-conditions-start
    requires |s| >= 2
    // pre-conditions-end
    // post-conditions-start
    ensures exists a, b : int :: des(s, a, b) && l == s[a] && h == s[b]
    ensures forall a, b : int :: des(s, a, b) ==> dist(l, h) <= dist(s[a], s[b])
    ensures l <= h
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  PairExists(s);
  var i := 0;
  var j := 1;
  var min_i := 0;
  var min_j := 1;
  var min_dist := dist(s[0], s[1]);
  
  while (i < |s|)
    invariant 0 <= i <= |s|
    invariant 0 <= j <= |s|
    invariant 0 <= min_i < |s|
    invariant 0 <= min_j < |s|
    invariant min_i != min_j
    invariant exists a, b: int :: des(s, a, b)
    invariant forall a, b: int :: 0 <= a < i && 0 <= b < |s| && a != b ==> min_dist == dist(s[min_i], s[min_j]) <= dist(s[a], s[b])
    invariant min_dist >= 0.0
  {
    j := 0;
    while (j < |s|)
      invariant 0 <= j <= |s|
      invariant i < |s|
      invariant 0 <= min_i < |s|
      invariant 0 <= min_j < |s|
      invariant min_i != min_j
      invariant forall a, b: int :: 0 <= a < i && 0 <= b < |s| && a != b ==> min_dist <= dist(s[a], s[b])
      invariant forall a, b: int :: 0 <= a < j && a != i ==> min_dist <= dist(s[a], s[i])
    {
      if (j != i) {
        var current_dist := dist(s[i], s[j]);
        if (current_dist < min_dist) {
          min_dist := current_dist;
          min_i := i;
          min_j := j;
        }
      }
      j := j + 1;
    }
    MinDistProperties(s, i, j, min_i, min_j);
    i := i + 1;
  }
  
  if (s[min_i] <= s[min_j]) {
    l, h := s[min_i], s[min_j];
  } else {
    l, h := s[min_j], s[min_i];
  }
}
// </vc-code>

