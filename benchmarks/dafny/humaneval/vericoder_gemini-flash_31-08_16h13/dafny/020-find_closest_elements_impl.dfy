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
    var min_dist := dist(s[0], s[1]);
    l := s[0];
    h := s[1];

    if l > h then (l, h) := (h, l); 

    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |s| >= 2
        invariant exists a_idx, b_idx :: des(s, a_idx, b_idx) && l == s[a_idx] && h == s[b_idx] && l <= h
        invariant forall a_idx, b_idx :: (0 <= a_idx < i && 0 <= b_idx < |s| && a_idx != b_idx) || (a_idx == i && 0 <= b_idx < i && a_idx != b_idx) ==> min_dist <= dist(s[a_idx], s[b_idx])
        invariant min_dist == dist(l, h)
    {
        var j := i + 1;
        while j < |s|
            invariant i < j <= |s|
            invariant |s| >= 2
            invariant exists a_idx, b_idx :: des(s, a_idx, b_idx) && l == s[a_idx] && h == s[b_idx] && l <= h
            invariant forall a_idx, b_idx :: (0 <= a_idx < i && 0 <= b_idx < |s| && a_idx != b_idx) || (a_idx == i && 0 <= b_idx < j && a_idx != b_idx) ==> min_dist <= dist(s[a_idx], s[b_idx])
            invariant min_dist == dist(l, h)
        {
            var current_dist := dist(s[i], s[j]);
            if current_dist < min_dist then
            {
                min_dist := current_dist;
                l := s[i];
                h := s[j];
                if l > h then (l, h) := (h, l); 
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

