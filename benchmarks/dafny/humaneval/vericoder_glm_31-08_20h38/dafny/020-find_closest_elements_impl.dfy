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
// </vc-helpers>
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
    l, h := s[0], s[1];
    if l > h {
        l, h := h, l;
    }

    for i := 0 to |s|-1
        invariant 0 <= i <= |s|
        invariant exists a, b : int :: des(s, a, b) && l == s[a] && h == s[b]
        invariant l <= h
        invariant forall a, b : int :: 0 <= a < i && a < b < |s| ==> dist(l, h) <= dist(s[a], s[b])
    {
        if i < |s|-1 {
            for j := i+1 to |s|-1
                invariant i+1 <= j <= |s|
                invariant exists a, b : int :: des(s, a, b) && l == s[a] && h == s[b]
                invariant l <= h
                invariant forall a, b : int :: 0 <= a < i && a < b < |s| ==> dist(l, h) <= dist(s[a], s[b])
                invariant forall b : int :: i+1 <= b < j ==> dist(l, h) <= dist(s[i], s[b])
            {
                var d_ij := dist(s[i], s[j]);
                if d_ij < dist(l, h) {
                    l, h := s[i], s[j];
                    if l > h {
                        l, h := h, l;
                    }
                }
            }
        }
    }
}
// </vc-code>

