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
    /* code modified by LLM (iteration 3): fixed invariants to properly track checked triplets */
    if nums.Length < 3 {
        result := false;
        return;
    }
    
    var i := 0;
    while i < nums.Length - 2
        invariant 0 <= i <= nums.Length - 2
        invariant forall x: int, y: int, z: int :: 0 <= x < y && y < z < nums.Length && x < i ==> !(nums[x] < nums[y] && nums[y] < nums[z])
    {
        var j := i + 1;
        while j < nums.Length - 1
            invariant i + 1 <= j <= nums.Length - 1
            invariant forall y: int, z: int :: i + 1 <= y < z < nums.Length && y < j ==> !(nums[i] < nums[y] && nums[y] < nums[z])
        {
            if nums[i] < nums[j] {
                var k := j + 1;
                while k < nums.Length
                    invariant j + 1 <= k <= nums.Length
                    invariant forall z: int :: j + 1 <= z < k ==> !(nums[i] < nums[j] && nums[j] < nums[z])
                {
                    if nums[j] < nums[k] {
                        result := true;
                        return;
                    }
                    k := k + 1;
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := false;
}
// </vc-code>
