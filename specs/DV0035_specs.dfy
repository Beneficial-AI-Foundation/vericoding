// <vc-preamble>
function CountMatches(xs: seq<nat>, x: nat): nat
    decreases |xs|
{
    if |xs| == 0 then
        0
    else
        var firstMatch: nat := if xs[0] == x then 1 else 0;
        firstMatch + CountMatches(xs[1..], x)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MajorityElement(xs: array<nat>) returns (result: nat)
    requires 
        xs.Length > 0
    requires
        exists x: nat :: CountMatches(xs[..], x) > xs.Length / 2
    ensures
        CountMatches(xs[..], result) > xs.Length / 2
// </vc-spec>
// <vc-code>
{
    // TODO: implement
    assume {:axiom} false;
    result := 0;
}
// </vc-code>
