function sum(cards: seq<int>): int
{
    if |cards| == 0 then 0
    else cards[0] + sum(cards[1..])
}

function abs(x: int): int
{
    if x >= 0 then x else -x
}

predicate ValidInput(cards: seq<int>, x: int)
{
    x > 0 && |cards| >= 1 && forall i :: 0 <= i < |cards| ==> -x <= cards[i] <= x
}

// <vc-helpers>
lemma SumBounds(cards: seq<int>, x: int)
    requires ValidInput(cards, x)
    ensures -x * |cards| <= sum(cards) <= x * |cards|
{
    if |cards| == 0 {
        assert sum(cards) == 0;
    } else {
        assert cards[0] >= -x && cards[0] <= x;
        if |cards| > 1 {
            SumBounds(cards[1..], x);
            assert sum(cards[1..]) >= -x * |cards[1..]|;
            assert sum(cards[1..]) <= x * |cards[1..]|;
            assert |cards[1..]| == |cards| - 1;
            assert sum(cards) == cards[0] + sum(cards[1..]);
        }
    }
}

lemma SumAppend(s: seq<int>, x: int)
    ensures sum(s + [x]) == sum(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert sum([x]) == x + sum([]);
        assert sum([]) == 0;
    } else {
        assert (s + [x])[0] == s[0];
        assert (s + [x])[1..] == s[1..] + [x];
        SumAppend(s[1..], x);
    }
}

lemma SumPrefix(cards: seq<int>, i: int)
    requires 0 <= i < |cards|
    ensures cards[..i+1] == cards[..i] + [cards[i]]
    ensures sum(cards[..i+1]) == sum(cards[..i]) + cards[i]
{
    assert cards[..i+1] == cards[..i] + [cards[i]];
    SumAppend(cards[..i], cards[i]);
}
// </vc-helpers>

// <vc-spec>
method solve(cards: seq<int>, x: int) returns (result: int)
    requires ValidInput(cards, x)
    ensures result >= 0
    ensures result == if sum(cards) == 0 then 0 else (abs(sum(cards)) + x - 1) / x
// </vc-spec>
// <vc-code>
{
    var s := 0;
    var i := 0;
    
    while i < |cards|
        invariant 0 <= i <= |cards|
        invariant s == sum(cards[..i])
    {
        s := s + cards[i];
        SumPrefix(cards, i);
        i := i + 1;
    }
    
    assert cards[..|cards|] == cards;
    assert s == sum(cards);
    
    if s == 0 {
        result := 0;
    } else {
        var absSum := if s >= 0 then s else -s;
        assert absSum == abs(s);
        assert absSum == abs(sum(cards));
        result := (absSum + x - 1) / x;
    }
}
// </vc-code>

