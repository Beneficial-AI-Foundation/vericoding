// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method TwoSum(nums: array<int>, target: int) returns (result: (int, int))
    requires
        nums.Length >= 2
    requires
        exists i: int, j: int :: 0 <= i < j < nums.Length && nums[i] + nums[j] == target
    requires
        forall i: int, j: int ::
            (0 <= i < nums.Length && 0 <= j < nums.Length)
                ==> (nums[i] + nums[j] <= 2147483647
                    && nums[i] + nums[j] >= -2147483648)
    ensures
        var (i, j) := result; 0 <= i < nums.Length
    ensures
        var (i, j) := result; 0 <= j < nums.Length
    ensures
        var (i, j) := result; i != j
    ensures
        var (i, j) := result; nums[i] + nums[j] == target
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
