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
    var minDist : real := dist(s[0], s[1]);
    var ia : int := 0;
    var ib : int := 1;
    for i := 0 to |s|-1 {
        for j := i+1 to |s|-1 {
            if dist(s[i], s[j]) < minDist {
                minDist := dist(s[i], s[j]);
                ia := i;
                ib := j;
            }
        }
    }
    l := if s[ia] <= s[ib] then s[ia] else s[ib];
    h := if s[ia] <= s[ib] then s[ib] else s[ia];
}
// </vc-code>

