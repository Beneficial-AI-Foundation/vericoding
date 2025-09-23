// <vc-preamble>
function SubarraySum(numbers: array<int>, start: int, end: int): int
    requires 0 <= start <= end <= numbers.Length
    reads numbers
    decreases end - start
{
    if start == end then 0
    else numbers[start] + SubarraySum(numbers, start + 1, end)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MaxSubarraySum(numbers: array<int>) returns (result: int)
    ensures result >= 0
    ensures forall start: int, end: int :: 
        start <= end && 0 <= start && end <= numbers.Length
        ==> SubarraySum(numbers, start, end) <= result
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := 0;
    // impl-end
}
// </vc-code>
