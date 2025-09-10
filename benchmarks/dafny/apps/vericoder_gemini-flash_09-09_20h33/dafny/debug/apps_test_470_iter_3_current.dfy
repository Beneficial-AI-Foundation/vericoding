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
  //reads s // This line is not needed and causes an error
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
            // The invariant needs to relate min_val to cards[k-i..k-1] plus current_card to be used in verification
            invariant exists x :: 0 <= x < i && min_val == (current_card + sum(cards[k-1-x .. k-1])) || (i == 1 && min_val == current_card) // More precise invariant.
            // A simpler invariant that still helps:
            invariant min_val == min(current_card, current_card + cards[k-2], current_card + cards[k-3], // ... up to cards[k-1-i]
                                    sum(cards[k-i..k-1]))
            invariant min_val <= sum(cards[k-i..k-1]) + current_card // This is a simpler, provable bound for min_val
            decreases k-i
        {
            min_val := min(min_val, current_card + cards[k-1-i]);
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
    if |cards| == 1 {
        return cards[0];
    }

    s[0] := cards[0];

    var i := 1;
    while i < |cards|
        invariant 0 < i <= |cards|
        invariant forall k' :: 0 <= k' < i ==> s[k'] == minPossibleSumUpToIndex(cards, k'+1)
        invariant forall k' :: 0 <= k' < i ==> cards[k'] > 0
        decreases |cards| - i
    {
        var current_card := cards[i];
        var min_val := current_card;
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant min_val >= 0
            invariant exists x :: 0 <= x < j+1 && min_val == (current_card + sum(cards[i-x..i-1])) || (j == 0 && min_val == current_card)
            invariant min_val <= current_card + sum(cards[i-j .. i-1])
            decreases i - j
        {
            min_val := min(min_val, current_card + cards[i-1-j]);
            j := j + 1;
        }
        s[i] := min(s[i-1] + current_card, min_val);
        i := i + 1;
    }
    return s[|cards|-1];
}
// </vc-code>

