predicate ValidInput(n: int, m: int, a: seq<int>) {
    n > 0 && m > 0 && |a| == n && forall i :: 0 <= i < |a| ==> a[i] > 0
}

predicate ValidResult(result: int, n: int) {
    1 <= result <= n
}

function SumCandiesStillNeeded(queue: seq<seq<int>>): nat
    requires forall child :: child in queue ==> |child| == 3 && child[0] >= 0 && child[1] > 0
{
    if |queue| == 0 then 0
    else
        var child := queue[0];
        var stillNeeded := if child[1] <= child[0] then 0 else child[1] - child[0];
        stillNeeded + SumCandiesStillNeeded(queue[1..])
}

// <vc-helpers>
predicate {:opaque} CanFulfill(child: seq<int>, candies: int) {
    child[1] <= child[0] + candies
}

function {:opaque} MaxCandiesInQueue(queue: seq<seq<int>>): int
    requires forall child :: child in queue ==> |child| == 3 && child[0] >= 0 && child[1] > 0
{
    if |queue| == 0 then 0
    else var child := queue[0];
         var remaining := MaxCandiesInQueue(queue[1..]);
         var stillNeeded := if child[1] <= child[0] then 0 else child[1] - child[0];
         if stillNeeded > remaining then stillNeeded else remaining
}

lemma SumCandiesStillNeeded_empty_or_single_child(queue: seq<seq<int>>)
    requires forall child :: child in queue ==> |child| == 3 && child[0] >= 0 && child[1] > 0
    ensures |queue| == 0 ==> SumCandiesStillNeeded(queue) == 0
    ensures |queue| == 1 ==> SumCandiesStillNeeded(queue) == (if queue[0][1] <= queue[0][0] then 0 else queue[0][1] - queue[0][0])
{
}

lemma SumCandiesStillNeeded_non_empty(queue: seq<seq<int>>)
    requires |queue| > 0
    requires forall child :: child in queue ==> |child| == 3 && child[0] >= 0 && child[1] > 0
    ensures SumCandiesStillNeeded(queue) == (var child := queue[0]; var stillNeeded := if child[1] <= child[0] then 0 else child[1] - child[0]; stillNeeded + SumCandiesStillNeeded(queue[1..]))
{
    // This lemma is directly implied by the function definition and doesn't need a specific body
    // beyond what Dafny's SMT solver can deduce from the function's recursive definition.
    // However, explicitly calling it out might help with more complex proofs involving this function.
}

lemma SumCandiesStillNeeded_drop_prefix(queue: seq<seq<int>>, k: nat)
    requires k <= |queue|
    requires forall child :: child in queue ==> |child| == 3 && child[0] >= 0 && child[1] > 0
    ensures SumCandiesStillNeeded(queue[k..]) >= 0
    decreases |queue| - k
    // Additional properties can be added here if needed for specific proofs
{
    if k == |queue| {
        assert SumCandiesStillNeeded(queue[k..]) == SumCandiesStillNeeded([]);
    } else if k < |queue| {
        var child_k := queue[k];
        var stillNeeded_k := if child_k[1] <= child_k[0] then 0 else child_k[1] - child_k[0];
        if k < |queue| -1 {
            SumCandiesStillNeeded_drop_prefix(queue, k + 1);
        }
        assert SumCandiesStillNeeded(queue[k..]) == stillNeeded_k + SumCandiesStillNeeded(queue[k+1..]);
    }
}

function min(a: int, b: int): int {
    if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, m, a)
    ensures ValidResult(result, n)
// </vc-spec>
// <vc-code>
{
    var queue: seq<seq<int>> := [];
    var i := 0;
    while i < n {
        queue := queue + [[a[i], a[i], i + 1]];
        i := i + 1;
    }

    var candies_given_total := 0;
    var max_candies_given_in_round := 0;

    while SumCandiesStillNeeded(queue) > 0
        invariant forall child :: child in queue ==> |child| == 3 && child[0] >= 0 && child[1] > 0
        invariant forall x :: x in queue ==> 0 <= x[2] <= n
        invariant (forall child1, child2 :: child1 in multiset(queue) && child2 in multiset(queue) && child1[2] == child2[2] ==> child1 == child2) || |queue| == 0 // Children are unique by their original index
        invariant forall child :: child in queue ==> child[0] <= child[1] // Current candies only grow, target fixed.
        invariant SumCandiesStillNeeded(queue) >= 0
        invariant candies_given_total % m == 0
        invariant max_candies_given_in_round == MaxCandiesInQueue(queue)
        decreases SumCandiesStillNeeded(queue)
    {
        max_candies_given_in_round := 0;
        var next_queue: seq<seq<int>> := [];
        var j := 0;
        while j < |queue|
            invariant forall child :: child in queue ==> |child| == 3 && child[0] >= 0 && child[1] > 0
            invariant forall x :: x in queue ==> 0 <= x[2] <= n
            invariant (forall child1, child2 :: child1 in multiset(queue) && child2 in multiset(queue) && child1[2] == child2[2] ==> child1 == child2) || |queue| == 0
            invariant forall child :: child in next_queue ==> |child| == 3 && child[0] >= 0 && child[1] >= child[0]
            invariant forall x :: x in next_queue ==> 0 <= x[2] <= n
            invariant (forall child1, child2 :: child1 in multiset(next_queue) && child2 in multiset(next_queue) && child1[2] == child2[2] ==> child1 == child2) || |next_queue| == 0
            invariant j <= |queue|
            invariant forall k :: 0 <= k < |next_queue| ==> next_queue[k][2] == queue[k][2]
            invariant max_candies_given_in_round >= 0
            invariant forall k :: 0 <= k < j ==>
                            (var child_prev := queue[k];
                             var current_candies_prev := child_prev[0];
                             var target_candies_prev := child_prev[1];
                             var candies_to_give_prev := if target_candies_prev <= current_candies_prev then 0 else min(m, target_candies_prev - current_candies_prev);
                             candies_to_give_prev <= max_candies_given_in_round)
            decreases |queue| - j
        {
            var child := queue[j];
            var current_candies := child[0];
            var target_candies := child[1];
            var original_idx := child[2];

            var candies_to_give := if target_candies <= current_candies then 0 else min(m, target_candies - current_candies);
            var new_current_candies := current_candies + candies_to_give;

            if candies_to_give > max_candies_given_in_round {
                max_candies_given_in_round := candies_to_give;
            }
            next_queue := next_queue + [[new_current_candies, target_candies, original_idx]];
            j := j + 1;
        }
        candies_given_total := candies_given_total + max_candies_given_in_round;

        // Filter out children who received enough candies
        var filtered_queue: seq<seq<int>> := [];
        var k := 0;
        while k < |next_queue|
            invariant forall child :: child in next_queue ==> |child| == 3 && child[0] >= 0 && child[1] >= child[0]
            invariant forall x :: x in next_queue ==> 0 <= x[2] <= n
            invariant (forall child1, child2 :: child1 in multiset(next_queue) && child2 in multiset(next_queue) && child1[2] == child2[2] ==> child1 == child2) || |next_queue| == 0
            invariant forall child :: child in filtered_queue ==> |child| == 3 && child[0] >= 0 && child[1] >= child[0]
            invariant forall x :: x in filtered_queue ==> 0 <= x[2] <= n
            invariant (forall child1, child2 :: child1 in multiset(filtered_queue) && child2 in multiset(filtered_queue) && child1[2] == child2[2] ==> child1 == child2) || |filtered_queue| == 0
            invariant k <= |next_queue|
            invariant forall child_check :: child_check in filtered_queue ==> child_check[0] < child_check[1]
            decreases |next_queue| - k
        {
            var child := next_queue[k];
            if child[0] < child[1] {
                filtered_queue := filtered_queue + [child];
            }
            k := k + 1;
        }
        queue := filtered_queue;
    }

    result := (candies_given_total - 1) / m + 1;
}
// </vc-code>

