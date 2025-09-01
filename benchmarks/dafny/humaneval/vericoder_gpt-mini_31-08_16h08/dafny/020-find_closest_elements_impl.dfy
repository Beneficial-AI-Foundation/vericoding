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
// no helpers required
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
  var n := |s|;
  var best_i := 0;
  var best_j := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= best_i < n && 0 <= best_j < n && best_i != best_j
    invariant forall a, b :: 0 <= a < n && 0 <= b < n && a < b && a < i ==> dist(s[best_i], s[best_j]) <= dist(s[a], s[b])
    decreases n - i
  {
    var j := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      invariant 0 <= best_i < n && 0 <= best_j < n && best_i != best_j
      invariant forall a, b :: 0 <= a < n && 0 <= b < n && a < b && (a < i || (a == i && b < j)) ==> dist(s[best_i], s[best_j]) <= dist(s[a], s[b])
      decreases n - j
    {
      if dist(s[i], s[j]) < dist(s[best_i], s[best_j]) {
        best_i := i;
        best_j := j;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  l := s[best_i];
  h := s[best_j];
  if l > h {
    var tmp := l;
    l := h;
    h := tmp;
  }
}
// </vc-code>

