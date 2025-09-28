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
  /* code modified by LLM (iteration 5): fixed syntax errors in ghost assert statements */
  var i: nat := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant forall k :: 0 <= k < i ==> CountOccurrences(nums[..], nums[k]) == 2
    invariant exists u :: u in nums[i..] && CountOccurrences(nums[..], u) == 1
  {
    var count: nat := 0;
    var j: nat := 0;
    while j < nums.Length
        invariant 0 <= j <= nums.Length
        invariant count == |set k :: 0 <= k < j && nums[k] == nums[i]|
    {
        if nums[j] == nums[i] {
            count := count + 1;
        }
        j := j + 1;
    }

    assert count == CountOccurrences(nums[..], nums[i]);

    if count == 1 {
      result := nums[i];
      return;
    }

    assert CountOccurrences(nums[..], nums[i]) == 2;
    
    ghost var u_exists :| u_exists in nums[i..] && CountOccurrences(nums[..], u_exists) == 1;
    assert u_exists != nums[i];
    assert u_exists in nums[i+1..];
    
    i := i + 1;
  }
}
// </vc-code>
