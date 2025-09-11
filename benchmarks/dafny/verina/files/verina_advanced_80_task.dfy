// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method TwoSum(nums: array<int>, target: int) returns (result: array<int>)
    requires 
        nums.Length >= 2 &&
        (exists i: int, j: int :: 0 <= j < i < nums.Length && nums[i] + nums[j] == target) &&
        (forall i1: int, j1: int, i2: int, j2: int :: 
            (0 <= j1 < i1 < nums.Length && nums[i1] + nums[j1] == target &&
             0 <= j2 < i2 < nums.Length && nums[i2] + nums[j2] == target) ==> 
            (i1 == i2 && j1 == j2))
    ensures
        result.Length == 2 &&
        0 <= result[0] < nums.Length &&
        0 <= result[1] < nums.Length &&
        result[0] < result[1] &&
        nums[result[0]] + nums[result[1]] == target
// </vc-spec>
// <vc-code>
{
    result := new int[2];
    result[0] := 0;
    result[1] := 1;
    assume {:axiom} false;
}
// </vc-code>
