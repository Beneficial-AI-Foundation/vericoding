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
function CountPairs(nums: seq<int>, x: int): nat
{
    if |nums| == 0 then 0
    else if nums[0] == x then 1 + CountPairs(nums[1..], x)
    else CountPairs(nums[1..], x)
}

/* helper modified by LLM (iteration 5): Fixed lemma with proper assertions */
lemma FilterEqualCountLemma(nums: seq<int>, x: int)
    ensures CountOccurrences(nums, x) == CountPairs(nums, x)
{
    if |nums| == 0 {
        // Base case: empty sequence
        assert CountOccurrences(nums, x) == 0;
        assert CountPairs(nums, x) == 0;
    } else {
        var head := nums[0];
        var tail := nums[1..];
        FilterEqualCountLemma(tail, x);
        
        if head == x {
            assert CountOccurrences(nums, x) == 1 + CountOccurrences(tail, x);
            assert CountPairs(nums, x) == 1 + CountPairs(tail, x);
        } else {
            assert CountOccurrences(nums, x) == CountOccurrences(tail, x);
            assert CountPairs(nums, x) == CountPairs(tail, x);
        }
    }
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
{
    /* code modified by LLM (iteration 5): Fixed XOR loop with proper invariant and conversion */
    var xor_result: bv32 := 0 as bv32;
    var i := 0;
    
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant xor_result == (if i > 0 then XORAll(nums[..i]) else 0 as bv32)
        decreases nums.Length - i
    {
        xor_result := xor_result ^ (nums[i] as bv32);
        i := i + 1;
    }
    
    result := xor_result as int;
}

function XORAll(nums: seq<int>): bv32
{
    if |nums| == 0 then 0 as bv32
    else (nums[0] as bv32) ^ XORAll(nums[1..])
}
// </vc-code>
