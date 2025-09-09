Given 5 cards with positive integers, find the minimum sum of remaining cards 
after optionally discarding exactly 2 or 3 cards that have the same number 
(at most one such discard operation allowed).

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

function sum(cards: seq<int>): int
    ensures |cards| > 0 && (forall i :: 0 <= i < |cards| ==> cards[i] > 0) ==> sum(cards) > 0
{
    if |cards| == 0 then 0
    else cards[0] + sum(cards[1..])
}

function count(cards: seq<int>, value: int): int
    ensures count(cards, value) >= 0
    ensures count(cards, value) <= |cards|
{
    if |cards| == 0 then 0
    else (if cards[0] == value then 1 else 0) + count(cards[1..], value)
}

function min(a: int, b: int): int
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a || min(a, b) == b
{
    if a <= b then a else b
}

function minPossibleSumUpToIndex(cards: seq<int>, idx: int): int
    requires |cards| == 5
    requires forall i :: 0 <= i < |cards| ==> cards[i] > 0
    requires 0 <= idx <= 5
    ensures minPossibleSumUpToIndex(cards, idx) >= 0
    ensures minPossibleSumUpToIndex(cards, idx) <= sum(cards)
{
    if idx == 0 then sum(cards)
    else
        var prevMin := minPossibleSumUpToIndex(cards, idx - 1);
        var cnt := count(cards, cards[idx - 1]);
        var removeCount := if cnt >= 3 then 3 else if cnt >= 2 then cnt else 0;
        if removeCount >= 2 then
            var newSum := sum(cards) - removeCount * cards[idx - 1];
            if newSum >= 0 then min(prevMin, newSum) else prevMin
        else
            prevMin
}

method solve(cards: seq<int>) returns (result: int)
    requires ValidInput(cards)
    ensures result >= 0
    ensures result <= sum(cards)
    ensures result == minPossibleSum(cards)
{
    result := sum(cards);

    var i := 0;
    while i < 5
        invariant 0 <= i <= 5
        invariant result >= 0
        invariant result <= sum(cards)
        invariant result == minPossibleSumUpToIndex(cards, i)
    {
        var cnt := count(cards, cards[i]);
        if cnt <= 3 {
            cnt := cnt;
        } else {
            cnt := 3;
        }

        if cnt == 2 || cnt == 3 {
            var newSum := sum(cards) - cnt * cards[i];
            if newSum >= 0 && newSum < result {
                result := newSum;
            }
        }

        i := i + 1;
    }

    assert result == minPossibleSum(cards);
}
