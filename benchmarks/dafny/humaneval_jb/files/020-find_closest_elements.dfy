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
  assume {:axiom} false;
}
// </vc-code>
