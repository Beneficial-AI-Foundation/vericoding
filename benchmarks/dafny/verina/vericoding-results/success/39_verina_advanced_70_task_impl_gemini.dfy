// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
function max(a: int, b: int): int { if a > b then a else b }
// </vc-helpers>

// <vc-spec>
method SemiOrderedPermutation(nums: array<int>) returns (result: int)
    ensures 
        result >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): adjusted loop invariant for variable i */
    var n := nums.Length;
    if n == 0 {
        result := 0;
        return;
    }

    var min_suffix := new int[n];
    min_suffix[n-1] := nums[n-1];
    var i := n - 2;
    while i >= 0
        invariant -1 <= i < n - 1
        invariant forall k :: i < k < n ==> (forall l :: k <= l < n ==> min_suffix[k] <= nums[l]) && (exists l :: k <= l < n && min_suffix[k] == nums[l])
    {
        min_suffix[i] := min(nums[i], min_suffix[i+1]);
        i := i - 1;
    }

    result := 1;
    if n > 1 {
        var max_so_far := nums[0];
        i := 0;
        while i < n - 1
            invariant 0 <= i <= n - 1
            invariant result >= 1
            invariant forall k :: 0 <= k <= i ==> max_so_far >= nums[k]
            invariant exists k :: 0 <= k <= i && max_so_far == nums[k]
            invariant forall k :: 0 <= k < n ==> (forall l :: k <= l < n ==> min_suffix[k] <= nums[l]) && (exists l :: k <= l < n && min_suffix[k] == nums[l])
        {
            if max_so_far <= min_suffix[i+1] {
                result := result + 1;
            }
            i := i + 1;
            max_so_far := max(max_so_far, nums[i]);
        }
    }
}
// </vc-code>
