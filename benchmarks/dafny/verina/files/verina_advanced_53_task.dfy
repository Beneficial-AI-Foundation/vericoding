// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MinimumRightShifts(nums: array<int>) returns (result: int)
    requires nums.Length <= 2147483647
    requires forall i, j :: 0 <= i < nums.Length && 0 <= j < nums.Length && i != j ==> nums[i] != nums[j]
    ensures
        var n := nums.Length;
        if n <= 1 then
            result == 0
        else
            (result >= 0 && result < n) || result == -1
// </vc-spec>
// <vc-code>
{
    // TODO: implement
    result := 0;
}
// </vc-code>
