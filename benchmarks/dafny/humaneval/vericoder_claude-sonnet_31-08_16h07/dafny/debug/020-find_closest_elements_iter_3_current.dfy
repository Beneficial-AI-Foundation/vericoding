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
lemma DistProperties(x: real, y: real)
    ensures dist(x, y) == dist(y, x)
    ensures dist(x, y) >= 0.0
{
}

lemma MinDistanceExists(s: seq<real>)
    requires |s| >= 2
    ensures exists a, b : int :: des(s, a, b) && 
            forall c, d : int :: des(s, c, d) ==> dist(s[a], s[b]) <= dist(s[c], s[d])
{
    var pairs := set a, b | 0 <= a < |s| && 0 <= b < |s| && a != b :: (a, b);
    assert (0, 1) in pairs;
    assert pairs != {};
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
    var min_i := 0;
    var min_j := 1;
    
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant des(s, min_i, min_j)
        invariant forall a, b : int :: des(s, a, b) && a < i ==> min_dist <= dist(s[a], s[b])
        invariant min_dist == dist(s[min_i], s[min_j])
    {
        var j := i + 1;
        while j < |s|
            invariant i + 1 <= j <= |s|
            invariant des(s, min_i, min_j)
            invariant forall a, b : int :: des(s, a, b) && a < i ==> min_dist <= dist(s[a], s[b])
            invariant forall b : int :: des(s, i, b) && i < b < j ==> min_dist <= dist(s[i], s[b])
            invariant min_dist == dist(s[min_i], s[min_j])
        {
            var current_dist := dist(s[i], s[j]);
            if current_dist < min_dist {
                min_dist := current_dist;
                min_i := i;
                min_j := j;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    if s[min_i] <= s[min_j] {
        l := s[min_i];
        h := s[min_j];
    } else {
        l := s[min_j];
        h := s[min_i];
    }
}
// </vc-code>

