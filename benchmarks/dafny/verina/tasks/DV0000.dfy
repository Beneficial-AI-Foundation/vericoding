// <vc-preamble>
// Helper function to count occurrences of an element in a sequence
function CountOccurrences(nums: seq<int>, x: int): nat
{
    |set i | 0 <= i < |nums| && nums[i] == x|
}

// Helper function to filter elements equal to x (recursive implementation)
function FilterEqual(nums: seq<int>, x: int): seq<int>
{
    if |nums| == 0 then []
    else if nums[0] == x then [nums[0]] + FilterEqual(nums[1..], x)
    else FilterEqual(nums[1..], x)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FindSingleNumber(nums: array<int>) returns (result: int)
    requires 
        nums.Length > 0
    requires
        exists unique_elem :: CountOccurrences(nums[..], unique_elem) == 1
    requires
        forall elem :: elem in nums[..] ==> (CountOccurrences(nums[..], elem) == 1 || CountOccurrences(nums[..], elem) == 2)
    ensures
        CountOccurrences(nums[..], result) == 1
    ensures
        forall x :: x in nums[..] ==> (x == result || CountOccurrences(nums[..], x) == 2)
// </vc-spec>
// <vc-code>
{
    // TODO: implement
    assume {:axiom} false;
    result := 0;
}
// </vc-code>
