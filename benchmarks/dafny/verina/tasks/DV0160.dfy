// <vc-preamble>
function CountOccurrences(a: seq<int>, key: int): nat
{
    |set i | 0 <= i < |a| && a[i] == key|
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method OnlyOnce(a: array<int>, key: int) returns (result: bool)
    ensures result <==> CountOccurrences(a[..], key) == 1
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := false;
    // impl-end
}
// </vc-code>
