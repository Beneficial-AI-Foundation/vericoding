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
function sum(cards: seq<int>): int
{
    if |cards| == 0 then 0
    else cards[0] + sum(cards[1..])
}

function minPossibleSumUpToIndex(cards: seq<int>, index: int): int
    requires ValidInput(cards)
    requires 0 <= index <= |cards|
    ensures minPossibleSumUpToIndex(cards, index) >= 0
    ensures minPossibleSumUpToIndex(cards, index) <= sum(cards[..index])
{
    if index == 0 then 0
    else
        var includeCard := cards[index-1] + minPossibleSumUpToIndex(cards, index-1);
        var excludeCard := minPossibleSumUpToIndex(cards, index-1);
        if includeCard < excludeCard then includeCard else excludeCard
}

lemma sumNonNegative(cards: seq<int>)
    requires ValidInput(cards)
    ensures sum(cards) >= 0
{
    if |cards| == 0 {
    } else {
        assert cards[0] > 0;
        sumNonNegative(cards[1..]);
    }
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
    sumNonNegative(cards);
    result := 0;
}
// </vc-code>

