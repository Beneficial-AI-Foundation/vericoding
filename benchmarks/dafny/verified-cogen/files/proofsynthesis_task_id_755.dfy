// <vc-preamble>
function MinSpec(s: seq<int>): int
    requires 0 < |s|
    decreases |s|
{
    if |s| == 1 then
        s[0]
    else if |s| == 0 then
        0
    else
        var laterMin := MinSpec(s[1..]);
        if s[0] <= laterMin then
            s[0]
        else
            laterMin
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SecondSmallest(numbers: array<int>) returns (indices: (int, int))
    requires numbers.Length >= 2
    ensures 0 <= indices.0 < numbers.Length && 0 <= indices.1 < numbers.Length
    ensures forall k :: 0 <= k < numbers.Length && k != indices.0 && numbers[indices.0] == MinSpec(numbers[..]) ==> numbers[k] >= numbers[indices.1]
    ensures exists k :: 0 <= k < numbers.Length && k != indices.0 && numbers[k] == numbers[indices.1]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
