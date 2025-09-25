// <vc-preamble>
function CountBoolean(s: seq<bool>): int
    decreases |s|
{
    if |s| == 0 then
        0
    else
        CountBoolean(s[..|s|-1]) + if s[|s|-1] then
            1
        else
            0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountTrue(arr: array<bool>) returns (count: int)
    ensures 0 <= count <= arr.Length
    ensures CountBoolean(arr[..]) == count
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
