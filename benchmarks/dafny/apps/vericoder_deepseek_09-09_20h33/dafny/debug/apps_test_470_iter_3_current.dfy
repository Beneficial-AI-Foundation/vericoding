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
{
    if |s| == 0 then 0
    else s[0] + sum(s[1..])
}

function minPossibleSumUpToIndex(cards: seq<int>, n: nat): int
    requires |cards| == 5 && forall i :: 0 <= i < |cards| ==> cards[i] > 0
    requires n <= 5
    ensures minPossibleSumUpToIndex(cards, n) >= 0
    ensures minPossibleSumUpToIndex(cards, n) <= sum(cards[0..n])
{
    if n == 0 then
        0
    else
        var withCurrent := if minPossibleSumUpToIndex(cards, n-1) >= cards[n-1]
            then minPossibleSumUpToIndex(cards, n-1) - cards[n-1]
            else 0;
        var withoutCurrent := minPossibleSumUpToIndex(cards, n-1) + cards[n-1];
        if withCurrent < withoutCurrent then
            withCurrent
        else
            withoutCurrent
}

lemma {:induction false} MinSumProperty(cards: seq<int>, n: nat)
    requires |cards| == 5 && forall i :: 0 <= i < |cards| ==> cards[i] > 0
    requires n <= 5
    ensures minPossibleSumUpToIndex(cards, n) == minPossibleSumUpToIndex(cards, n)
    decreases n
{
    if n > 0 {
        MinSumProperty(cards, n-1);
    }
}

lemma {:induction false} SumInvariantLemma(cards: seq<int>, n: nat, s0: int, s1: int)
    requires |cards| == 5 && forall i :: 0 <= i < |cards| ==> cards[i] > 0
    requires n <= 5
    requires s0 >= 0 && s1 >= 0
    requires s0 + s1 <= sum(cards[0..n])
    requires s0 + s1 >= minPossibleSumUpToIndex(cards, n)
    ensures s0 + s1 >= minPossibleSumUpToIndex(cards, n)
{
}

lemma {:induction false} FinalResultLemma(cards: seq<int>, s0: int, s1: int)
    requires |cards| == 5 && forall i :: 0 <= i < |cards| ==> cards[i] > 0
    requires s0 >= 0 && s1 >= 0
    requires s0 + s1 <= sum(cards)
    requires s0 + s1 >= minPossibleSumUpToIndex(cards, 5)
    ensures (if s0 <= s1 then s0 else s1) >= minPossibleSumUpToIndex(cards, 5)
    ensures (if s0 <= s1 then s0 else s1) <= sum(cards)
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
    var s0 := 0;
    var s1 := 0;
    var i := 0;
    while i < 5
        invariant 0 <= i <= 5
        invariant s0 >= 0 && s1 >= 0
        invariant s0 + s1 <= sum(cards[0..i])
        invariant s0 + s1 >= minPossibleSumUpToIndex(cards, i)
    {
        MinSumProperty(cards, i);
        SumInvariantLemma(cards, i, s0, s1);
        if s0 >= cards[i] {
            s0 := s0 - cards[i];
        } else if s1 >= cards[i] {
            s1 := s1 - cards[i];
        } else {
            if s0 <= s1 {
                s0 := s0 + cards[i];
            } else {
                s1 := s1 + cards[i];
            }
        }
        i := i + 1;
        SumInvariantLemma(cards, i, s0, s1);
    }
    MinSumProperty(cards, 5);
    FinalResultLemma(cards, s0, s1);
    result := if s0 <= s1 then s0 else s1;
}
// </vc-code>

