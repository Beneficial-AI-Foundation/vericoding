// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): original implementation was empty; this re-submits the empty helper section */
// </vc-helpers>

// <vc-spec>
method LongestIncreasingStreak(nums: array<int>) returns (result: nat)
    ensures
        (nums.Length == 0 ==> result == 0) &&
        result <= nums.Length
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed indexing for loop invariant and provided an assertion for currentLength and maxLength */
{
    if nums.Length == 0 {
        return 0;
    }

    var maxLength := 0;
    var currentLength := 0;
    var i := 0;

    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant 0 <= maxLength <= i
        invariant (i > 0 && currentLength > 0 ==> currentLength <= i)
        invariant (i == 0 ==> currentLength == 0)
        invariant maxLength <= nums.Length
    {
        if i == 0 || nums[i-1] >= nums[i] {
            currentLength := 1;
        } else {
            currentLength := currentLength + 1;
        }

        if currentLength > maxLength {
            maxLength := currentLength;
        }

        i := i + 1;
    }

    return maxLength;
}
// </vc-code>
