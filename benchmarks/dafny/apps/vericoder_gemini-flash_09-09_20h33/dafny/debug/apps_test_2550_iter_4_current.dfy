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
    
    var current_sum_rem_others := total_left_to_distribute;
    var current_redistributed_len := 1;

    while current_redistributed_len < n
        invariant 1 <= current_redistributed_len <= n
        invariant current_redistributed_len > 0 ==> new_redistributed[0] == desired_first_score
        invariant |new_redistributed| == current_redistributed_len
        invariant forall i :: 0 <= i < |new_redistributed| ==> 0 <= new_redistributed[i] <= m
        invariant Sum(new_redistributed) == original_sum - current_sum_rem_others
        invariant current_sum_rem_others >= 0 // crucial for val_for_k
        invariant current_sum_rem_others <= (n - current_redistributed_len) * m
        decreases n - current_redistributed_len
    {
        var val_for_k := min(m, current_sum_rem_others);
        
        assert val_for_k >= 0; // Follows from current_sum_rem_others >= 0
        assert val_for_k <= m; // Follows from min definition

        new_redistributed := new_redistributed + [val_for_k];
        current_sum_rem_others := current_sum_rem_others - val_for_k;
        current_redistributed_len := current_redistributed_len + 1;
        assert current_sum_rem_others >= 0; // Property must be maintained
    }

    // After the loop, we must show current_sum_rem_others == 0
    // The total sum of elements (excluding the first) that can be distributed is (n-1)*m.
    // `total_left_to_distribute` is `original_sum - desired_first_score`.
    // Since `original_sum <= n*m` and `desired_first_score >= 0`.
    // `total_left_to_distribute <= n*m`.
    // Also, `total_left_to_distribute >= 0` by pre-condition `Sum(scores) >= desired_first_score`.
    // Each iteration distributes at most `m`. We do `n-1` iterations.
    // So `current_sum_rem_others` must eventually be 0.
    assert current_redistributed_len == n;
    assert current_sum_rem_others >= 0;
    assert current_sum_rem_others <= (n - current_redistributed_len) * m;
    assert current_sum_rem_others <= (n - n) * m;
    assert current_sum_rem_others <= 0;
    assert current_sum_rem_others == 0;
    
    var final_redistributed := new_redistributed;
    assert |final_redistributed| == n;
    assert Sum(final_redistributed) == original_sum - current_sum_rem_others;
    assert Sum(final_redistributed) == original_sum;
    assert final_redistributed[0] == desired_first_score;
    assert forall i :: 0 <= i < |final_redistributed| ==> 0 <= final_redistributed[i] <= m;
    
    assert ValidRedistribution(scores, final_redistributed, m);
    assert final_redistributed[0] == desired_first_score;
    assert |final_redistributed| == n;
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

    // Establish conditions for lemma_redistribution_exists
    assert 0 <= first_score <= m; // From min definition and m >= 1
    assert sum_scores >= first_score; // From min definition

    lemma_redistribution_exists(n, m, scores, first_score);

    return first_score;
}
// </vc-code>

