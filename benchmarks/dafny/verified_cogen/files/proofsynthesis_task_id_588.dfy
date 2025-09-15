// <vc-preamble>
function MaxRcur(s: seq<int>): int
    requires |s| > 0
    decreases |s|
{
    if |s| <= 1 then
        s[0]
    else
        var last := s[|s|-1];
        var rest := MaxRcur(s[..|s|-1]);
        if last > rest then last else rest
}

function MinRcur(s: seq<int>): int
    requires |s| > 0
    decreases |s|
{
    if |s| <= 1 then
        s[0]
    else
        var last := s[|s|-1];
        var rest := MinRcur(s[..|s|-1]);
        if last < rest then last else rest
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method DifferenceMaxMin(arr: array<int>) returns (diff: int)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> -1073741824 < arr[i] < 1073741823
    ensures diff == MaxRcur(arr[..]) - MinRcur(arr[..])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
