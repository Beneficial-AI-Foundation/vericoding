// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SemiOrderedPermutation(nums: array<int>) returns (result: int)
    ensures 
        result >= 0
// </vc-spec>
// <vc-code>
{
    var n := nums.Length;
    if n == 0 {
        result := 0;
    } else {
        var idx1 := -1;
        for i := 0 to n
        {
            if nums[i] == 1 {
                idx1 := i;
                break;
            }
        }

        var idxn := -1;
        for i := 0 to n
        {
            if nums[i] == n {
                idxn := i;
                break;
            }
        }

        if idx1 == -1 || idxn == -1 {
            result := 0;
        } else {
            result := idx1 + (n - 1 - idxn);
            if idx1 > idxn {
                result := result - 1;
            }
        }
    }
}
// </vc-code>
