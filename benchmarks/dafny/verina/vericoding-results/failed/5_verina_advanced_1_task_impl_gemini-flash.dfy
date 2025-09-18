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
/* helper modified by LLM (iteration 5): No changes were made as helpers are not related to the current compilation error. */
function FilterWithPredicate(s: seq<int>, p: int -> bool): seq<int>
{
    if |s| == 0 then []
    else if p(s[0]) then [s[0]] + FilterWithPredicate(s[1..], p)
    else FilterWithPredicate(s[1..], p)
}

function Sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + Sum(s[1..])
}
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
/* code modified by LLM (iteration 5): The error `RandomElement()` on `set<int>` implies it's not a valid operation for sets. Removed the use of `RandomElement()` and instead used `seenOnlyOnce.Any()` followed by an `iterator` and `var` declaration to assign the single element to `result` */
{
    var seenOnlyOnce: set<int> := {};
    var seenTwice: set<int> := {};

    for i := 0 to nums.Length - 1
        invariant 0 <= i <= nums.Length
        invariant forall x :: x in seenTwice ==> CountOccurrences(nums[..i], x) == 2
        invariant forall x :: x in seenOnlyOnce ==> CountOccurrences(nums[..i], x) == 1
        invariant forall x :: x in seenOnlyOnce ==> x !in seenTwice
        invariant forall x :: x in seenTwice ==> x !in seenOnlyOnce
    {
        var num := nums[i];
        if num in seenOnlyOnce {
            seenOnlyOnce := seenOnlyOnce - {num};
            seenTwice := seenTwice + {num};
        } else if num !in seenTwice {
            seenOnlyOnce := seenOnlyOnce + {num};
        }
    }
    
    // After the loop, the 'single number' is the only one remaining in seenOnlyOnce
    // because all numbers appearing twice would have moved to seenTwice.
    assert |seenOnlyOnce| == 1;
    
    // Iterate through the set to get the single element
    var iter := seenOnlyOnce.Iterator();
    iter.Next();
    result := iter.Get();
}
// </vc-code>
