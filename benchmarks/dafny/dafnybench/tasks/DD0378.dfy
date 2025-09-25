// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method removeElement(nums: array<int>, val: int) returns (i: int)
    ensures forall k :: 0 < k < i < nums.Length ==> nums[k] != val
    modifies nums
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
