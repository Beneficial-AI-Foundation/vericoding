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
function min(a: real, b: real): real {
  if a <= b then a else b
}

function max(a: real, b: real): real {
  if a >= b then a else b
}

function is_sorted(s: seq<real>): bool {
  forall k :: 0 <= k < |s| - 1 ==> s[k] <= s[k+1]
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
    var closest_l: real := s[0];
    var closest_h: real := s[1];
    var min_dist: real := dist(s[0], s[1]);

    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant exists a, b :: des(s, a, b) && ( (closest_l == s[a] && closest_h == s[b]) || (closest_h == s[a] && closest_l == s[b]) )
        invariant forall x, y :: 0 <= x < i && 0 <= y < |s| && x != y ==> min_dist <= dist(s[x], s[y]) // Changed from 'i' to '|s|' for y, as y can be anywhere in s for outer loop invariant.
        invariant min_dist == dist(closest_l, closest_h)
    {
        var j := i + 1;
        while j < |s|
            invariant i < j <= |s|
            invariant 0 <= i < |s|
            invariant exists a, b :: des(s, a, b) && ( (closest_l == s[a] && closest_h == s[b]) || (closest_h == s[a] && closest_l == s[b]) )
            invariant forall x, y :: ( (0 <= x < i && 0 <= y < |s|) || (x == i && i < y < j) ) && x != y ==> min_dist <= dist(s[x], s[y])
            invariant min_dist == dist(closest_l, closest_h)
        {
            if dist(s[i], s[j]) < min_dist
            {
                min_dist := dist(s[i], s[j]);
                closest_l := s[i];
                closest_h := s[j];
            }
            j := j + 1;
        }
        i := i + 1;
    }

    l := min(closest_l, closest_h);
    h := max(closest_l, closest_h);
}
// </vc-code>

