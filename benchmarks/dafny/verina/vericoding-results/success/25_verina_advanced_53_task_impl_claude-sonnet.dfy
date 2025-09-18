// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed problematic helpers causing verification issues */
function IsSorted(nums: array<int>): bool
    reads nums
{
    forall i, j :: 0 <= i < j < nums.Length ==> nums[i] <= nums[j]
}
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
    /* code modified by LLM (iteration 3): fixed array bounds and simplified implementation */
    var n := nums.Length;
    if n <= 1 {
        result := 0;
        return;
    }
    
    var temp := new int[n];
    var i := 0;
    while i < n {
        temp[i] := nums[i];
        i := i + 1;
    }
    
    // Sort the temporary array
    var k := 0;
    while k < n - 1 {
        var minIdx := k;
        var j := k + 1;
        while j < n {
            if j < temp.Length && minIdx < temp.Length && temp[j] < temp[minIdx] {
                minIdx := j;
            }
            j := j + 1;
        }
        if k < temp.Length && minIdx < temp.Length {
            var tempVal := temp[k];
            temp[k] := temp[minIdx];
            temp[minIdx] := tempVal;
        }
        k := k + 1;
    }
    
    // Check each possible rotation
    var shifts := 0;
    result := -1; // Initialize result to default value
    while shifts < n
        decreases n - shifts
    {
        var isMatch := true;
        var idx := 0;
        while idx < n && isMatch {
            if nums[(idx + shifts) % n] != temp[idx] {
                isMatch := false;
            }
            idx := idx + 1;
        }
        if isMatch {
            result := shifts;
            break;
        }
        shifts := shifts + 1;
    }
}
// </vc-code>
