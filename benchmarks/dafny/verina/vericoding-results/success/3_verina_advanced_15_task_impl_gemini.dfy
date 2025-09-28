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
    /* code modified by LLM (iteration 2): [add loop invariants to prove postconditions] */
    var i := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant forall i_ : int, j_ : int, k_ : int ::
            0 <= i_ < i && i_ < j_ && j_ < k_ < nums.Length ==>
            !(nums[i_] < nums[j_] && nums[j_] < nums[k_])
    {
        var j := i + 1;
        while j < nums.Length
            invariant 0 <= i < nums.Length
            invariant i < j <= nums.Length
            invariant forall j_ : int, k_ : int ::
                i < j_ < j && j_ < k_ < nums.Length ==>
                !(nums[i] < nums[j_] && nums[j_] < nums[k_])
        {
            var k := j + 1;
            while k < nums.Length
                invariant 0 <= i < j < nums.Length
                invariant j < k <= nums.Length
                invariant forall k_ : int ::
                    j < k_ < k ==>
                    !(nums[i] < nums[j] && nums[j] < nums[k_])
            {
                if nums[i] < nums[j] && nums[j] < nums[k] {
                    result := true;
                    return;
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    result := false;
}
// </vc-code>
