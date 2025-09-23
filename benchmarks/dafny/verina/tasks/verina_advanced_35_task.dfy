// <vc-preamble>
function CountOccurrences(nums: seq<int>, x: int): nat
    decreases |nums|
{
    if |nums| == 0 then
        0
    else
        var first := nums[0];
        var restCount := CountOccurrences(nums[1..], x);
        if first == x then
            restCount + 1
        else
            restCount
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MajorityElement(nums: seq<int>) returns (result: int)
    requires 
        |nums| > 0 &&
        exists x :: CountOccurrences(nums, x) > |nums| / 2
    ensures 
        CountOccurrences(nums, result) > |nums| / 2 &&
        forall x :: x != result ==> CountOccurrences(nums, x) <= |nums| / 2
// </vc-spec>
// <vc-code>
{
    // TODO: implement
    assume {:axiom} false;
    result := 0;
}
// </vc-code>
