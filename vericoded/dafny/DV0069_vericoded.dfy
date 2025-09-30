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
    /* code modified by LLM (iteration 2): ensure result is always non-negative */
    if nums.Length == 0 {
        result := 0;
        return;
    }
    
    var pos1 := 0;
    var posN := 0;
    
    for i := 0 to nums.Length
    {
        if nums[i] == 1 {
            pos1 := i;
        }
        if nums[i] == nums.Length {
            posN := i;
        }
    }
    
    if pos1 < posN {
        result := pos1 + (nums.Length - 1 - posN);
    } else if pos1 > posN {
        result := pos1 + (nums.Length - 1 - posN) - 1;
    } else {
        result := 0;
    }
    
    if result < 0 {
        result := 0;
    }
}
// </vc-code>
