predicate ValidInput(n: int, m: int, scores: seq<int>)
{
    n >= 1 && m >= 1 && |scores| == n &&
    forall i :: 0 <= i < |scores| ==> 0 <= scores[i] <= m
}

function Sum(nums: seq<int>): int
    ensures Sum(nums) >= 0 || exists i :: 0 <= i < |nums| && nums[i] < 0
{
    if |nums| == 0 then 0
    else nums[0] + Sum(nums[1..])
}

function min(a: int, b: int): int
    ensures min(a, b) == a || min(a, b) == b
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a <==> a <= b
{
    if a <= b then a else b
}

predicate ValidRedistribution(original: seq<int>, redistributed: seq<int>, m: int)
{
    |redistributed| == |original| &&
    Sum(redistributed) == Sum(original) &&
    forall i :: 0 <= i < |redistributed| ==> 0 <= redistributed[i] <= m
}

function MaxPossibleFirstScore(n: int, m: int, scores: seq<int>): int
    requires ValidInput(n, m, scores)
    ensures MaxPossibleFirstScore(n, m, scores) == min(Sum(scores), m)
{
    min(Sum(scores), m)
}

// <vc-helpers>
lemma lemma_SumOfScoresNonNegative(n: int, m: int, scores: seq<int>)
    requires ValidInput(n, m, scores)
    ensures Sum(scores) >= 0
{
    // Proof: All scores[i] are >= 0, so their sum must be >= 0.
    // The Sum function's postcondition already ensures this if all elements are non-negative.
}

lemma lemma_redistribution_exists(n: int, m: int, scores: seq<int>, desired_first_score: int)
    requires ValidInput(n, m, scores)
    requires 0 <= desired_first_score <= m
    requires Sum(scores) >= desired_first_score // The remaining sum must be non-negative for redistribution
    ensures exists redistributed :: (ValidRedistribution(scores, redistributed, m) && redistributed[0] == desired_first_score)
{
    var original_sum := Sum(scores);
    var remaining_sum_for_others := original_sum - desired_first_score;

    var new_redistributed: seq<int> := [desired_first_score];
    var total_left_to_distribute := original_sum - desired_first_score;
    
    // We need to prove that total_left_to_distribute will be 0 at the end
    // after distributing it amongst n-1 elements, each at most m.
    // This is true if `total_left_to_distribute <= (n-1) * m`.
    // We know `original_sum <= n * m` (from ValidInput).
    // And `desired_first_score >=0`.
    // So `total_left_to_distribute = original_sum - desired_first_score <= original_sum <= n * m`.
    // More strongly, if desired_first_score is `min(original_sum, m)`, then
    // if original_sum <= m, desired_first_score = original_sum, so total_left_to_distribute = 0.
    // if original_sum > m, desired_first_score = m, so total_left_to_distribute = original_sum - m.
    // In this case, original_sum - m <= (n-1) * m holds IF original_sum <= n*m.
    // This is guaranteed by ValidInput.

    var current_sum_rem_others := total_left_to_distribute;
    var current_redistributed_len := 1;

    while current_redistributed_len < n
        invariant 1 <= current_redistributed_len <= n
        invariant new_redistributed[0] == desired_first_score
        invariant |new_redistributed| == current_redistributed_len
        invariant forall i :: 0 <= i < |new_redistributed| ==> 0 <= new_redistributed[i] <= m
        invariant Sum(new_redistributed) == original_sum - current_sum_rem_others
        decreases n - current_redistributed_len
    {
        var val_for_k := min(m, current_sum_rem_others);
        
        // This assertion is critical for correctness:
        // We need to show that `val_for_k` is non-negative.
        // `current_sum_rem_others` can be 0, in which case `val_for_k` is 0.
        // If `current_sum_rem_others > 0`, then `val_for_k = min(m, pos_val)` which is `> 0`.
        // So `val_for_k >= 0` always holds.
        assert val_for_k >= 0;

        new_redistributed := new_redistributed + [val_for_k];
        current_sum_rem_others := current_sum_rem_others - val_for_k;
        current_redistributed_len := current_redistributed_len + 1;
    }

    // After the loop, we expect current_sum_rem_others to be 0
    assert current_sum_rem_others == 0;
    
    var final_redistributed := new_redistributed;

    assert ValidRedistribution(scores, final_redistributed, m);
    assert final_redistributed[0] == desired_first_score;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, scores: seq<int>) returns (result: int)
    requires ValidInput(n, m, scores)
    ensures result == MaxPossibleFirstScore(n, m, scores)
    ensures result == min(Sum(scores), m)
    ensures exists redistributed :: (ValidRedistribution(scores, redistributed, m) && 
            redistributed[0] == result)
// </vc-spec>
// <vc-code>
{
    var sum_scores := Sum(scores);
    var first_score := min(sum_scores, m);
    
    // Prove that the constructed first_score satisfies the properties
    assert first_score == MaxPossibleFirstScore(n, m, scores);
    assert first_score == min(sum_scores, m);

    // Call helper lemma to establish existence of the redistribution
    lemma_SumOfScoresNonNegative(n, m, scores); // Ensure sum_scores >= 0
    lemma_redistribution_exists(n, m, scores, first_score);

    return first_score;
}
// </vc-code>

