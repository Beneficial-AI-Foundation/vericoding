// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Adding max function */
function max(a: int, b: int): int { if a > b then a else b }
// </vc-helpers>

// <vc-spec>
method LongestIncreasingStreak(nums: array<int>) returns (result: nat)
    ensures
        (nums.Length == 0 ==> result == 0) &&
        result <= nums.Length
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed unresolved identifier by adding a max helper function */
{
    if nums.Length == 0 {
        result := 0;
        return;
    }

    var maxLength := 0;
    var currentLength := 0;

    for i := 0 to nums.Length
        invariant 0 <= i <= nums.Length
        invariant 0 <= maxLength <= i
        invariant 0 <= currentLength <= i
        invariant maxLength <= nums.Length
        invariant (i == 0 || nums.Length == 0) ==> (currentLength == 0 && maxLength == 0)
        invariant (i > 0 && nums.Length > 0) ==> (currentLength > 0 ==> forall j :: i - currentLength <= j < i - 1 ==> nums[j] < nums[j+1])
    
    {
        if i == 0 {
            currentLength := 1;
        } else if i < nums.Length && nums[i-1] < nums[i] {
            currentLength := currentLength + 1;
        } else {
            maxLength := max(maxLength, currentLength);
            currentLength := 1;
        }
    }
    maxLength := max(maxLength, currentLength);
    result := maxLength;
}
// </vc-code>
