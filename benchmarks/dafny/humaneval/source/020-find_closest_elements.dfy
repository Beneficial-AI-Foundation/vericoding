function dist(a: real, b: real) : (d : real)
    ensures d >= 0.0
    ensures (d == 0.0) <==> a == b
{
    if a < b then b - a else a - b
}
// pure-end

function des(s: seq<real>, a: int, b: int) : bool {
    // distinct elements
    0 <= a < |s| && 0 <= b < |s| && a != b
}
// pure-end
method find_closest_elements(s: seq<real>) returns (l : real, h : real)
    // pre-conditions-start
    requires |s| >= 2
    // pre-conditions-end
    // post-conditions-start
    ensures exists a, b : int :: des(s, a, b) && l == s[a] && h == s[b]
    ensures forall a, b : int :: des(s, a, b) ==> dist(l, h) <= dist(s[a], s[b])
    ensures l <= h
    // post-conditions-end
{
    // impl-start
    l := s[0];
    h := s[1];
    var d : real := dist(l, h);
    for i := 0 to |s|
        // invariants-start
        invariant d == dist(l, h)
        invariant exists a, b :: des(s, a, b) && l == s[a] && h == s[b]
        invariant forall a, b :: a < i && des(s, a, b) ==> d <= dist(s[a], s[b])
        // invariants-end
    {
        for j := i + 1 to |s|
            // invariants-start
            invariant d == dist(l, h)
            invariant exists a, b :: des(s, a, b) && l == s[a] && h == s[b]
            invariant forall a, b :: (a < i || (a == i && b < j)) && des(s, a, b) ==> d <= dist(s[a], s[b])
            // invariants-end
        {
            if dist(s[i], s[j]) <= d {
                l := s[i];
                h := s[j];
                d := dist(l, h);
            }
        }
    }
    if (l <= h) {
        return l, h;
    } else {
        return h, l;
    }
    // impl-end
}
