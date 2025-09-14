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
    var n := nums.Length;
    if n <= 1 {
        result := 0;
        return;
    }
    
    var sorted := new int[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
    {
        sorted[i] := nums[i];
        i := i + 1;
    }
    
    // Simple bubble sort
    var outer := 0;
    while outer < n - 1
        invariant 0 <= outer <= n - 1
    {
        var inner := 0;
        while inner < n - 1 - outer
            invariant 0 <= inner <= n - 1 - outer
        {
            if sorted[inner] > sorted[inner + 1] {
                var temp := sorted[inner];
                sorted[inner] := sorted[inner + 1];
                sorted[inner + 1] := temp;
            }
            inner := inner + 1;
        }
        outer := outer + 1;
    }
    
    // Try each possible rotation
    var shifts := 0;
    while shifts < n
        invariant 0 <= shifts <= n
    {
        var matches := true;
        var j := 0;
        while j < n && matches
            invariant 0 <= j <= n
        {
            if nums[(j + shifts) % n] != sorted[j] {
                matches := false;
            }
            j := j + 1;
        }
        
        if matches {
            result := shifts;
            return;
        }
        shifts := shifts + 1;
    }
    
    result := -1;
}
// </vc-code>
