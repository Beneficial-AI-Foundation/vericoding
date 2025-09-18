// <vc-preamble>
function CountOccurrences(nums: seq<int>, value: int): nat
{
    |set i | 0 <= i < |nums| && nums[i] == value|
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MajorityElement(nums: array<int>) returns (result: int)
    requires nums.Length > 0
    ensures var numsSeq := nums[..];
            var n := |numsSeq|;
            CountOccurrences(numsSeq, result) > n / 2 &&
            forall x: int :: x == result || CountOccurrences(numsSeq, x) <= n / 2
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The Boyer-Moore Majority Vote algorithm is used to find the majority element. The algorithm is based on the idea that if an element is the majority element, it will eventually be identified as the candidate. If the problem statement guarantees there is always a majority element, then the candidate at the end of the first pass of the Boyer-Moore algorithm is the majority element. Therefore, no second pass is needed. */
{
  var candidate := nums[0];
  var count := 0;

  for i := 0 to nums.Length - 1
    invariant 0 <= i <= nums.Length
    invariant count >= 0
    invariant (count == 0 || (exists k :: 0 <= k < i && nums[k] == candidate))
  {
    if count == 0 {
      candidate := nums[i];
      count := 1;
    } else if nums[i] == candidate {
      count := count + 1;
    } else {
      count := count - 1;
    }
  }

  result := candidate;
}
// </vc-code>
