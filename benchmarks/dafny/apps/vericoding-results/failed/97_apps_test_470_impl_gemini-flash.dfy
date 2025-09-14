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
  // Changed ensures clause to only guarantee non-negativity if all elements are non-negative.
  // The original problem statement indicates cards[i] > 0, so this should hold.
  ensures (forall x :: x in s ==> x > 0) ==> sum(s) >= 0
{
  if s == [] then 0 else s[0] + sum(s[1..])
}

function min(a: int, b: int): int {
    if a < b then a else b
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
        // This loop calculates the minimum sum ending at `cards[k-1]`, which could be just `cards[k-1]` or `cards[k-1] + cards[k-2]` etc.
        // It's effectively calculating `min(cards[k-1], cards[k-1] + cards[k-2], cards[k-1] + cards[k-2] + cards[k-3], ...)`.
        var current_suffix_sum := 0; // Represents the sum of elements `cards[k-2]` down to `cards[k-1-x]`
        while i < k
            invariant 1 <= i <= k
            invariant current_card > 0
            invariant min_val >= 0
            invariant current_suffix_sum == sum(cards[k-i .. k-2]) // invariant for current_suffix_sum
            // min_val is the minimum of current_card + sum(cards[k-j .. k-2]) for j from 1 to i-1, and current_card
            invariant min_val == min(current_card, current_card + min(set x | 0 <= x < i-1 :: sum(cards[k-1-x .. k-2]))) // this is for understanding, slightly complex for Dafny
            // A more direct invariant for `min_val` based on its update rule:
            // At the start of iteration `i`, `min_val` holds `min(cards[k-1], cards[k-1]+cards[k-2], ..., cards[k-1]+sum(cards[k-i+1..k-2]))`
            invariant min_val == (if i==1 then current_card else min(set x | 0 <= x < i-1 :: current_card + sum(cards[k-1-x .. k-2])))
            decreases k - i
        {
            // Update current_suffix_sum to include the next card (cards[k-1-i])
            current_suffix_sum := current_suffix_sum + cards[k-1-i];
            min_val := min(min_val, current_card + current_suffix_sum);
            i := i + 1;
        }
        // The result for minPossibleSumUpToIndex(cards, k) is the minimum of:
        // 1. the best sum ending at cards[k-1], and
        // 2. the best sum ending at cards[k-2] plus cards[k-1].
        min(prev_sums + current_card, min_val)
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

    var i := 1; // current index we are calculating s[i] for
    while i < |cards|
        invariant 0 < i <= |cards|
        invariant forall k' :: 0 <= k' < i ==> s[k'] == minPossibleSumUpToIndex(cards, k'+1)
        invariant forall k' :: 0 <= k' < |cards| ==> cards[k'] > 0
        decreases |cards| - i
    {
        var current_card := cards[i];
        // min_ending_here represents the minimum sum of a suffix ending at cards[i].
        // This could be cards[i] itself, or cards[i] + cards[i-1], or cards[i] + cards[i-1] + cards[i-2], etc.
        var min_ending_here := current_card;
        var current_suffix_sum := 0; // Represents sum of cards from j down to i-1 (inclusive) where j is the iteration variable in the inner loop (but relative to the outer loop's i)
        var j := 1; // j for iterating backwards from i-1
        while j <= i
            invariant 1 <= j <= i + 1 // j can go up to i. If j=1, sum(cards[i-1..i-1]). If j=i, sum(cards[0..i-1]).
            invariant current_card > 0
            invariant min_ending_here >= 0
            // current_suffix_sum holds sum(cards[i-j .. i-1])
            invariant current_suffix_sum == (if j==1 then 0 else sum(cards[i-j+1 .. i-1]))
            invariant min_ending_here == min(set x | 0 <= x < j :: (current_card + (if x == 0 then 0 else sum(cards[i-x .. i-1]))))
            decreases i - j
        {
            if j <= i { // Ensure we don't access out of bounds for cards[i-j]
                 current_suffix_sum := current_suffix_sum + cards[i-j];
                 min_ending_here := min(min_ending_here, current_card + current_suffix_sum);
            }
            j := j + 1;
        }
        s[i] := min(s[i-1] + current_card, min_ending_here);
        i := i + 1;
    }
    return s[|cards|-1];
}
// </vc-code>

