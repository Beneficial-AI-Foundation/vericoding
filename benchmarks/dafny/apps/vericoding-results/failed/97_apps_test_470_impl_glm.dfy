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
    decreases |s|
{
    if |s| == 0 then 0 else s[|s|-1] + sum(s[..|s|-1])
}

function minPossibleSumUpToIndex(cards: seq<int>, k: int): int
    requires 0 <= k <= |cards|
    requires forall i :: 0 <= i < |cards| ==> cards[i] >= 0
    ensures minPossibleSumUpToIndex(cards, k) >= 0
    ensures minPossibleSumUpToIndex(cards, k) <= sum(cards[..k])
    decreases k
{
    if k == 0 then 0 else minPossibleSumUpToIndex(cards, k-1)
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
    return minPossibleSum(cards);
}
// </vc-code>

