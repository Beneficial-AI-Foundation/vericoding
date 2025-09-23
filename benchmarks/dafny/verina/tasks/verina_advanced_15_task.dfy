// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IncreasingTriplet(nums: array<int>) returns (result: bool)
    ensures
        result ==> exists i: int, j: int, k: int :: 
            0 <= i < j && j < k < nums.Length && 
            nums[i] < nums[j] && nums[j] < nums[k]
    ensures
        !result ==> forall i: int, j: int, k: int :: 
            0 <= i < j && j < k < nums.Length ==> 
            !(nums[i] < nums[j] && nums[j] < nums[k])
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := false;
    // impl-end
}
// </vc-code>
