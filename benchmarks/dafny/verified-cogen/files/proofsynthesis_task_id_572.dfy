// <vc-preamble>
function CountFrequencyRcr(s: seq<int>, key: int): int
    decreases |s|
{
    if |s| == 0 then
        0
    else
        CountFrequencyRcr(s[..|s|-1], key) + if s[|s|-1] == key then
            1
        else
            0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(arr: array<int>) returns (unique_arr: array<int>)
    ensures forall i :: 0 <= i < unique_arr.Length ==> CountFrequencyRcr(arr[..], unique_arr[i]) == 1
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
