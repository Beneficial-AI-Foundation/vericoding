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
// No updates needed in helpers
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
    var minDist : real := 0.0;  // Initialize to avoid definite-assignment issues
    var ia : int := 0;
    var ib : int := 1;
    var initialized := false;
    var i := 0;
    while i < |s| 
        invariant 0 <= i <= |s|
        invariant initialized ==> (0 <= ia < |s| && 0 <= ib < |s| && ia != ib && s[ia] != s[ib] && minDist == dist(s[ia], s[ib]))
        invariant initialized ==> forall a, b :: 0 <= a < |s| && 0 <= b < |s| && a != b && initialized ==> dist(s[ia], s[ib]) <= dist(s[a], s[b])
        decreases |s| - i
    {
        var j := i + 1;
        while j < |s| 
            invariant i + 1 <= j <= |s|
            invariant initialized ==> (0 <= ia < |s| && 0 <= ib < |s| && ia != ib && s[ia] != s[ib] && minDist == dist(s[ia], s[ib]))
            invariant initialized ==> forall a, b :: 0 <= a < |s| && 0 <= b < |s| && a != b && initialized ==> dist(s[ia], s[ib]) <= dist(s[a], s[b])
            decreases |s| - j
        {
            var d := dist(s[i], s[j]);
            if !initialized || d < minDist {
                minDist := d;
                ia := i;
                ib := j;
                initialized := true;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    // Since |s| >= 2, initialized will be true
    l := if s[ia] <= s[ib] then s[ia] else s[ib];
    h := if s[ia] <= s[ib] then s[ib] else s[ia];
}
// </vc-code>

