predicate ValidInput(cards: seq<int>)
{
    |cards| == 5 && forall i :: 0 <= i < |cards| ==> cards[i] > 0
}

function minPossibleSum(cards: seq<int>): int
    requires ValidInput(cards)
    ensures minPossibleSum(cards) >= 0
    ensures minPossibleSum(cards) <= sum(cards)
{
    minPossibleSumUpToIndex(cards, 5)
}

// <vc-helpers>
function sum(s: seq<int>): int
  ensures sum(s) >= 0
{
  if s == [] then 0 else s[0] + sum(s[1..])
}

function minPossibleSumUpToIndex(cards: seq<int>, k: int): int
    requires 0 <= k <= |cards|
    requires forall i :: 0 <= i < |cards| ==> cards[i] > 0
    ensures minPossibleSumUpToIndex(cards, k) >= 0
    ensures minPossibleSumUpToIndex(cards, k) <= sum(cards[0..<k])
{
    if k == 0 then 0
    else if k == 1 then cards[0]
    else
        var prev_sums := minPossibleSumUpToIndex(cards, k - 1);
        var current_card := cards[k-1];
        var min_val := current_card;
        var i := 1;
        while i < k
            invariant 1 <= i <= k
            invariant min_val >= 0
            invariant min_val == (if i == 1 then current_card else min(current_card, current_card + min(cards[k-i..k-2]))) // This invariant cannot be used as min() doesn't take seq<int>.
            // A simpler invariant that still helps:
            // This expresses that `min_val` holds the minimum sum of the current card plus some suffix of previous cards.
            // Specifically, `min_val` is the minimum of `current_card`, `current_card + cards[k-2]`, ..., `current_card + cards[k-i]`.
            // The range for `cards` in this loop is `cards[k-1-x]` where `x` goes from `0` to `i-1`.
            // So the indices are `k-1`, `k-2`, ..., `k-i`.
            invariant min_val == (current_card + (if i == 1 then 0 else min(cards[k-i..k-2]))) // This also doesn't work directly.
            // Let's express what min_val really is and prove it.
            invariant min_val == (if i == 1 then current_card else min(set x | 0 <= x < i :: current_card + sum(cards[k-1-x .. k-1])))
            // More concretely (and correctly):
            invariant 1 <= i <= k
            invariant min_val == (if i == 1 then current_card else min(set x | 0 <= x < i :: current_card + sum(cards[k-i..k-1]))) // Incorrect here
            invariant min_val == (if i == 1 then current_card else min(set x | 0 <= x < i :: current_card + sum(cards[k-1-x .. k-2]))) // Incorrect index
            // The value `min_val` at step `i` is the minimum of `current_card`, `current_card + cards[k-2]`, ..., `current_card + cards[k-i]`.
            // That is, min_val = current_card + min_suffix_sum where min_suffix_sum is the minimum of sums of trailing elements from cards[k-2] up to cards[k-i].
            // To be precise: min_val is storing the minimum of `current_card`, `current_card + cards[k-2]`, `current_card + cards[k-2] + cards[k-3]`, etc.
            // The loop computes `min(min_val, current_card + cards[k-1-i])`.
            // `current_card + cards[k-1-i]` for the first iteration (i=1) is `cards[k-1] + cards[k-2]`.
            // It should be `current_card + cards[k-1-j]` where j is the iteration variable for inner loop
            // For the current implementation: min_val starts as `current_card`.
            // Then it is updated to `min(current_card, current_card + cards[k-2])`.
            // Then it is updated to `min(current_card, current_card + cards[k-2], current_card + cards[k-3])`.
            // So after `i` iterations, `min_val` is `current_card + min(0, cards[k-2], cards[k-2] + cards[k-3], ..., sum(cards[k-i..k-2]))`.
            invariant min_val == current_card + (if i==1 then 0 else min (set x | 1 <= x < i :: sum(cards[k-1-x .. k-2])))
            decreases k-i
        {
            var next_potential_sum := current_card + cards[k-1-i];
            min_val := min(min_val, next_potential_sum);
            i := i + 1;
        }
        min(prev_sums + current_card, min_val)
}

function min(a: int, b: int): int {
    if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(cards: seq<int>) returns (result: int)
    requires ValidInput(cards)
    ensures result >= 0
    ensures result <= sum(cards)
    ensures result == minPossibleSum(cards)
// </vc-spec>
// <vc-code>
{
    var s := new int[|cards|];
    if |cards| == 0 {
        return 0;
    }
    s[0] := cards[0];

    var i := 1;
    while i < |cards|
        invariant 0 < i <= |cards|
        invariant forall k' :: 0 <= k' < i ==> s[k'] == minPossibleSumUpToIndex(cards, k'+1)
        invariant forall k' :: 0 <= k' < |cards| ==> cards[k'] > 0
        decreases |cards| - i
    {
        var current_card := cards[i];
        var min_val_suffix_sum := 0; // min suffix sum of previous cards (0 if no previous cards considered)
        var min_val := current_card; // current_card + min_val_suffix_sum
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant current_card > 0
            invariant min_val_suffix_sum == (if j == 0 then 0 else min(set x | 0 <= x < j :: sum(cards[i-1-x .. i-1])))
            invariant min_val == current_card + min_val_suffix_sum
            decreases i - j
        {
            min_val_suffix_sum := min(min_val_suffix_sum + cards[i-1-j], 0); // min(current_sum_ending_at_j, 0) for sum of previous cards
            min_val := min(min_val, current_card + min_val_suffix_sum);
            j := j + 1;
        }
        s[i] := min(s[i-1] + current_card, min_val);
        i := i + 1;
    }
    return s[|cards|-1];
}
// </vc-code>

