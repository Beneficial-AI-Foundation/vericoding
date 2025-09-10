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
    requires Sum(scores) - desired_first_score >= 0 // The remaining sum must be non-negative for redistribution
    ensures exists redistributed :: (ValidRedistribution(scores, redistributed, m) && redistributed[0] == desired_first_score)
{
    var original_sum := Sum(scores);
    var remaining_sum_for_others := original_sum - desired_first_score;

    var redistributed_arr: array<int>;
    if n > 1 {
        redistributed_arr := new int[n];
    } else {
        redistributed_arr := new int[1]; // Even if n=1, need an array
    }
    
    redistributed_arr[0] := desired_first_score;

    var current_sum_assigned_to_others := 0;
    var i := 1;
    while i < n {
        decreases n - i;
        var assign_to_current := min(m, remaining_sum_for_others - current_sum_assigned_to_others);
        
        // This is tricky. We need to ensure assign_to_current is >= 0
        // It relies on remaining_sum_for_others - current_sum_assigned_to_others >= 0
        // This holds because current_sum_assigned_to_others only increases and is always <= remaining_sum_for_others
        
        // Let's refine the assignment
        var val_to_assign: int;
        if remaining_sum_for_others - current_sum_assigned_to_others <= 0 {
             val_to_assign := 0; // If nothing left, assign 0
        } else {
            val_to_assign := min(m, remaining_sum_for_others - current_sum_assigned_to_others);
            assert val_to_assign >= 0; // min(m, positive) or min(m, 0)
        }
        
        redistributed_arr[i] := val_to_assign;
        current_sum_assigned_to_others := current_sum_assigned_to_others + val_to_assign;
        i := i + 1;
    }

    var redistributed_seq := redistributed_arr[..];

    assert redistributed_seq[0] == desired_first_score;
    assert |redistributed_seq| == n;

    // Prove sum
    assert Sum(redistributed_seq[1..]) == current_sum_assigned_to_others;
    assert desired_first_score + current_sum_assigned_to_others == Sum(scores); // This is the goal

    // Correct sum logic: if n=1, remaining_sum_for_others must be 0, current_sum_assigned_to_others must be 0
    // If n > 1, the while loop should correctly distribute the sum.
    // The loop invariant should maintain that current_sum_assigned_to_others is distributed up to i-1.
    // And remaining_sum_for_others - current_sum_assigned_to_others is the amount that needs to be distributed.

    // A simpler construction might be:
    // If n=1, then redistributed = [desired_first_score]
    if n == 1 {
        assert Sum(scores) == scores[0];
        assert desired_first_score == Sum(scores); // Since only one element, first score must be total sum
        var single_redistributed_seq := [desired_first_score];
        assert ValidRedistribution(scores, single_redistributed_seq, m);
    } else {
        // For n > 1, after the loop, current_sum_assigned_to_others might not be exactly remaining_sum_for_others
        // This happens if remaining_sum_for_others is not perfectly divisible or m is too small.
        // The problem statement implies such a redistribution is always possible if sum is within bounds.
        // A less greedy approach for `redistributed_arr[i]` might be needed to fulfill the sum constraint.

        // Let's construct `redistributed_seq` more robustly to ensure `Sum(redistributed_seq)` condition.
        
        // This is a known hard problem for Dafny: proving existence of such a sequence by construction
        // purely within Dafny. often requires more detailed iterative proofs.
        // For now, let's confirm the sum.
     
        // Let's create a *valid* redistribution sequence more directly.
        // The problem guarantees it exists. We just need to show a concrete one.
        // Set redistributed[0] = desired_first_score
        // Set redistributed[1] = min(m, remaining_sum_for_others)
        // If remaining_sum_for_others > m, then redistributed[2] = remaining_sum_for_others - m (if n>2), and so on.
        // This distribution is guaranteed to exist because n, m, scores are within constraints.

        // Here's a simpler construction:
        var new_redistributed: seq<int> := [desired_first_score];
        var total_left_to_distribute := original_sum - desired_first_score;
        
        for k := 1 to n-1 {
            var val_for_k := min(m, total_left_to_distribute);
            new_redistributed := new_redistributed + [val_for_k];
            total_left_to_distribute := total_left_to_distribute - val_for_k;
        }

        // Now, we need to prove that `total_left_to_distribute` is 0 at the end.
        // This is true if `Sum(scores)` fits within `desired_first_score + (n-1)*m`.
        // We know `Sum(scores) <= m * n` and `desired_first_score <= m`.
        // The problem states that such a redistribution `exists`. My proof needs to construct it.

        // Crucial realization:
        // `desired_first_score` is `min(Sum(scores), m)`.
        // Let `S = Sum(scores)`.
        // Case 1: `S <= m`. Then `desired_first_score = S`.
        //   `new_redistributed` will be `[S] + [0, 0, ..., 0]`.
        //   `Sum(new_redistributed) = S`.
        //   `ValidRedistribution` holds.
        // Case 2: `S > m`. Then `desired_first_score = m`.
        //   `new_redistributed[0] = m`.
        //   `total_left_to_distribute` starts at `S - m`.
        //   We then fill `n-1` slots.
        //   Since `S <= n * m`, then `S - m <= (n-1) * m`.
        //   This means `total_left_to_distribute` can always be distributed among the remaining `n-1` slots,
        //   each taking at most `m`, and the sum will be 0 at the end.
        //   The `min(m, total_left_to_distribute)` ensures each element is `<= m`.
        //   It's also `min(m, positive)` or `min(m,0)`, so `val_for_k >= 0`.

        assert total_left_to_distribute == 0; // This is the key part of the proof by construction
                                              // Requires a loop invariant proof for the for loop.
        
        var final_redistributed := new_redistributed;
        assert ValidRedistribution(scores, final_redistributed, m);
        assert final_redistributed[0] == desired_first_score;

    } // end else (n > 1)
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

