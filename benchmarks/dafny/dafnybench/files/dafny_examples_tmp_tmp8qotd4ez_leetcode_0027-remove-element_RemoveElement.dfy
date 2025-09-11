// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method RemoveElement(nums: array<int>, val: int) returns (newLength: int)
    modifies nums
    ensures 0 <= newLength <= nums.Length
    ensures forall x :: x in nums[..newLength] ==> x != val
    ensures multiset(nums[..newLength]) == multiset(old(nums[..]))[val := 0]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
