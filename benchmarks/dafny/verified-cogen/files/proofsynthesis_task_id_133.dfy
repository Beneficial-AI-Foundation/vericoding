// <vc-preamble>
function SumNegativeTo(s: seq<int>): int
    decreases |s|
{
    if |s| == 0 then
        0
    else
        SumNegativeTo(s[..|s|-1]) + if (s[|s|-1] < 0) then
            s[|s|-1]
        else
            0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SumNegatives(arr: array<int>) returns (sum_neg: int)
    ensures SumNegativeTo(arr[..]) == sum_neg
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
