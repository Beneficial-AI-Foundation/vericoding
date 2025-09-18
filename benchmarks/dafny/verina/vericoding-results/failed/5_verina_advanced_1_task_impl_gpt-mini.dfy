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
/* helper modified by LLM (iteration 5): relate CountOccurrences and FilterEqual lengths */
lemma CountEqualsFilter(nums: seq<int>, x: int)
  ensures CountOccurrences(nums, x) == |FilterEqual(nums, x)|
  decreases |nums|
{
  if |nums| == 0 {
    // both sides are 0 by definitions
  } else {
    var tail := nums[1..];
    CountEqualsFilter(tail, x);
    if nums[0] == x {
      // unfold definitions: CountOccurrences adds 1 for index 0, FilterEqual prepends element
      assert CountOccurrences(nums, x) == 1 + CountOccurrences(tail, x);
      assert |FilterEqual(nums, x)| == 1 + |FilterEqual(tail, x)|;
      assert CountOccurrences(nums, x) == |FilterEqual(nums, x)|;
    } else {
      // element at head does not contribute
      assert CountOccurrences(nums, x) == CountOccurrences(tail, x);
      assert |FilterEqual(nums, x)| == |FilterEqual(tail, x)|;
      assert CountOccurrences(nums, x) == |FilterEqual(nums, x)|;
    }
  }
}

/* helper modified by LLM (iteration 5): find an index of an element appearing exactly once using a loop */
method IndexOfCountOne(nums: seq<int>, x: int) returns (i: int)
  requires CountOccurrences(nums, x) == 1
  ensures 0 <= i < |nums| && nums[i] == x
  decreases |nums|
{
  var k := 0;
  while k < |nums|
    decreases |nums| - k
  {
    if nums[k] == x {
      i := k;
      return;
    }
    k := k + 1;
  }
  // impossible because requires says there is exactly one occurrence
  assert false;
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
  /* code modified by LLM (iteration 5): linear search to find the element whose CountOccurrences is 1 */
  var n := nums.Length;
  var i := 0;
  while i < n
    decreases n - i
  {
    if CountOccurrences(nums[..], nums[i]) == 1 {
      result := nums[i];
      return;
    }
    i := i + 1;
  }
  // precondition guarantees existence of such an element
  assert false;
}

// </vc-code>
