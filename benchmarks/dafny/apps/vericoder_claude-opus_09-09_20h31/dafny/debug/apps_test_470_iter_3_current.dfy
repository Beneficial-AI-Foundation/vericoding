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

function minElement(cards: seq<int>): int
    requires |cards| > 0
    requires forall i :: 0 <= i < |cards| ==> cards[i] > 0
    ensures minElement(cards) > 0
    ensures forall i :: 0 <= i < |cards| ==> minElement(cards) <= cards[i]
    ensures exists i :: 0 <= i < |cards| && minElement(cards) == cards[i]
{
    if |cards| == 1 then
        cards[0]
    else
        var restMin := minElement(cards[1..]);
        if cards[0] <= restMin then cards[0] else restMin
}

function minPossibleSumUpToIndex(cards: seq<int>, index: int): int
    requires ValidInput(cards)
    requires 0 <= index <= |cards|
    ensures minPossibleSumUpToIndex(cards, index) >= 0
    ensures index > 0 ==> minPossibleSumUpToIndex(cards, index) > 0
    ensures index > 0 ==> minPossibleSumUpToIndex(cards, index) <= sum(cards[..index])
    decreases index
{
    if index == 0 then
        0
    else 
        minElement(cards[..index])
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

lemma sumNonNegative(cards: seq<int>)
    requires forall i :: 0 <= i < |cards| ==> cards[i] > 0
    ensures sum(cards) >= 0
    ensures |cards| > 0 ==> sum(cards) > 0
{
    if |cards| == 0 {
    } else {
        sumNonNegative(cards[1..]);
    }
}

lemma sumSliceProperty(cards: seq<int>, i: int)
    requires 0 <= i < |cards|
    ensures sum(cards[..i+1]) == sum(cards[..i]) + cards[i]
{
    var prefix := cards[..i];
    var extended := cards[..i+1];
    
    assert extended == prefix + [cards[i]];
    
    calc == {
        sum(extended);
        sum(prefix + [cards[i]]);
        {sumAppend(prefix, [cards[i]]);}
        sum(prefix) + sum([cards[i]]);
        sum(prefix) + cards[i];
        sum(cards[..i]) + cards[i];
    }
}

lemma sumAppend(s1: seq<int>, s2: seq<int>)
    ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        calc == {
            sum(s1 + s2);
            sum([s1[0]] + s1[1..] + s2);
            {assert [s1[0]] + s1[1..] + s2 == [s1[0]] + (s1[1..] + s2);}
            sum([s1[0]] + (s1[1..] + s2));
            s1[0] + sum(s1[1..] + s2);
            {sumAppend(s1[1..], s2);}
            s1[0] + sum(s1[1..]) + sum(s2);
            sum(s1) + sum(s2);
        }
    }
}

lemma minElementInSum(cards: seq<int>)
    requires |cards| > 0
    requires forall i :: 0 <= i < |cards| ==> cards[i] > 0
    ensures minElement(cards) <= sum(cards)
{
    if |cards| == 1 {
        assert minElement(cards) == cards[0] == sum(cards);
    } else {
        var m := minElement(cards);
        assert exists i :: 0 <= i < |cards| && m == cards[i];
        sumNonNegative(cards);
        assert sum(cards) >= cards[0];
    }
}

lemma minPossibleSumCorrect(cards: seq<int>)
    requires ValidInput(cards)
    ensures minPossibleSum(cards) == minPossibleSumUpToIndex(cards, 5)
{
}

lemma minPossibleSumBounds(cards: seq<int>)
    requires ValidInput(cards)
    ensures minPossibleSum(cards) <= sum(cards)
{
    assert minPossibleSum(cards) == minPossibleSumUpToIndex(cards, 5);
    assert minPossibleSumUpToIndex(cards, 5) == minElement(cards[..5]);
    assert cards[..5] == cards;
    minElementInSum(cards);
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
    var minVal := cards[0];
    var i := 1;
    
    while i < 5
        invariant 1 <= i <= 5
        invariant minVal == minElement(cards[..i])
        invariant minVal > 0
    {
        if cards[i] < minVal {
            minVal := cards[i];
        }
        i := i + 1;
    }
    
    assert cards[..5] == cards;
    assert minVal == minElement(cards);
    assert minVal == minPossibleSumUpToIndex(cards, 5);
    minPossibleSumBounds(cards);
    
    result := minVal;
}
// </vc-code>

