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
/* helper modified by LLM (iteration 4): added lemma to prove outer loop invariant and postcondition */
lemma OuterLoopInvariantHelper(s: seq<real>, l: real, h: real, i: int)
  requires |s| >= 2
  requires 0 <= i <= |s|
  requires exists a, b : int :: des(s, a, b) && l == s[a] && h == s[b]
  requires forall a, b : int :: des(s, a, b) && a < i && b < i ==> dist(l, h) <= dist(s[a], s[b])
  requires forall k : int :: 0 <= k < i ==> (forall m : int :: k + 1 <= m < |s| ==> dist(l, h) <= dist(s[k], s[m]))
  ensures forall a, b : int :: des(s, a, b) && a < i ==> dist(l, h) <= dist(s[a], s[b])
{
  forall a, b | des(s, a, b) && a < i
    ensures dist(l, h) <= dist(s[a], s[b])
  {
    if b < i {
      // This case is covered by the first precondition
    } else {
      // b >= i, so by the second precondition we have dist(l, h) <= dist(s[a], s[b])
    }
  }
}
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
  /* code modified by LLM (iteration 4): fixed invariants to be provable with proper helper lemma */
  var min_dist := dist(s[0], s[1]);
  l := s[0];
  h := s[1];
  if l > h {
    l := s[1];
    h := s[0];
  }
  
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant exists a, b : int :: des(s, a, b) && l == s[a] && h == s[b]
    invariant forall a, b : int :: des(s, a, b) && a < i && b < i ==> dist(l, h) <= dist(s[a], s[b])
    invariant forall k : int :: 0 <= k < i ==> (forall m : int :: k + 1 <= m < |s| ==> dist(l, h) <= dist(s[k], s[m]))
    invariant l <= h
  {
    var j := i + 1;
    while j < |s|
      invariant i + 1 <= j <= |s|
      invariant exists a, b : int :: des(s, a, b) && l == s[a] && h == s[b]
      invariant forall a, b : int :: des(s, a, b) && a < i && b < i ==> dist(l, h) <= dist(s[a], s[b])
      invariant forall k : int :: 0 <= k < i ==> (forall m : int :: k + 1 <= m < |s| ==> dist(l, h) <= dist(s[k], s[m]))
      invariant forall m : int :: i + 1 <= m < j ==> dist(l, h) <= dist(s[i], s[m])
      invariant l <= h
    {
      var curr_dist := dist(s[i], s[j]);
      if curr_dist < dist(l, h) {
        if s[i] <= s[j] {
          l := s[i];
          h := s[j];
        } else {
          l := s[j];
          h := s[i];
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
  OuterLoopInvariantHelper(s, l, h, |s|);
}
// </vc-code>
