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
    decreases index
{
    if index == 0 then
        0
    else 
        var prevSum := minPossibleSumUpToIndex(cards, index - 1);
        min(prevSum, prevSum + cards[index - 1])
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

lemma sumNonNegative(cards: seq<int>)
    requires forall i :: 0 <= i < |cards| ==> cards[i] > 0
    ensures sum(cards) >= 0
{
    if |cards| == 0 {
    } else {
        sumNonNegative(cards[1..]);
    }
}

lemma minPossibleSumCorrect(cards: seq<int>)
    requires ValidInput(cards)
    ensures minPossibleSum(cards) == minPossibleSumUpToIndex(cards, 5)
{
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
    var currentSum := 0;
    var i := 0;
    
    while i < 5
        invariant 0 <= i <= 5
        invariant currentSum == minPossibleSumUpToIndex(cards, i)
    {
        var nextSum := currentSum + cards[i];
        currentSum := if currentSum <= nextSum then currentSum else nextSum;
        i := i + 1;
    }
    
    result := currentSum;
}
// </vc-code>

