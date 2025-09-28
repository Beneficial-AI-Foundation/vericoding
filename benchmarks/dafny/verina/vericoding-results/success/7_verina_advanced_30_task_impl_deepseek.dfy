// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fix predicate with reads clause and improve lemma */
predicate IsIncreasingStreak(nums: array<int>, start: nat, len: nat)
    requires start + len <= nums.Length
    reads nums
{
    if len <= 1 then
        true
    else
        forall i :: start <= i < start + len - 1 ==> nums[i] < nums[i + 1]
}

function max(a: nat, b: nat): nat {
    if a > b then a else b
}

lemma StreakBoundaryLemma(nums: array<int>, currentStreak: nat, currentPos: nat, bestSoFar: nat)
    requires 0 <= currentPos <= nums.Length
    requires currentStreak <= nums.Length
    requires bestSoFar <= nums.Length
    decreases nums.Length - currentPos
{
}
// </vc-helpers>

// <vc-spec>
method LongestIncreasingStreak(nums: array<int>) returns (result: nat)
    ensures
        (nums.Length == 0 ==> result == 0) &&
        result <= nums.Length
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fix implementation with proper loop invariants and streak tracking */
{
    if nums.Length == 0 {
        result := 0;
        return;
    }
    
    var currentStreak: nat := 1;
    result := 1;
    var i: nat := 1;
    
    while i < nums.Length
        invariant i <= nums.Length
        invariant currentStreak <= nums.Length
        invariant result <= nums.Length
        invariant 1 <= currentStreak <= i
        invariant result >= currentStreak
        invariant i - currentStreak <= nums.Length
    {
        if nums[i - 1] < nums[i] {
            currentStreak := currentStreak + 1;
        } else {
            currentStreak := 1;
        }
        result := max(result, currentStreak);
        i := i + 1;
    }
}
// </vc-code>
