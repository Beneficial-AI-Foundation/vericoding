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
        
        // Prove ValidInput for the suffix
        assert |cards[1..]| >= 0;
        assert forall i :: 0 <= i < |cards[1..]| ==> -x <= cards[1..][i] <= x by {
            forall i | 0 <= i < |cards[1..]|
                ensures -x <= cards[1..][i] <= x
            {
                assert cards[1..][i] == cards[i + 1];
                assert 0 <= i + 1 < |cards|;
                assert -x <= cards[i + 1] <= x;
            }
        }
        
        if |cards[1..]| >= 1 {
            assert ValidInput(cards[1..], x);
            SumBounds(cards[1..], x);
        }
        
        assert -x * |cards[1..]| <= sum(cards[1..]) <= x * |cards[1..]|;
        assert |cards[1..]| == |cards| - 1;
        assert sum(cards) == cards[0] + sum(cards[1..]);
        assert sum(cards) >= -x + (-x * (|cards| - 1)) == -x * |cards|;
        assert sum(cards) <= x + (x * (|cards| - 1)) == x * |cards|;
    }
}

lemma DivisionProperty(a: int, b: int)
    requires b > 0
    requires a > 0
    ensures (a + b - 1) / b >= 1
    ensures (a + b - 1) / b == (a - 1) / b + 1
{
    calc {
        (a + b - 1) / b;
        == { assert a + b - 1 == (a - 1) + b; }
        ((a - 1) + b) / b;
        == { ModuloArithmetic(a - 1, b); }
        (a - 1) / b + 1;
    }
    
    assert a >= 1;
    assert a + b - 1 >= b;
    assert (a + b - 1) / b >= 1;
}

lemma ModuloArithmetic(a: int, b: int)
    requires b > 0
    ensures (a + b) / b == a / b + 1
{
    var q := a / b;
    var r := a % b;
    assert a == q * b + r && 0 <= r < b;
    assert a + b == q * b + r + b == (q + 1) * b + r;
    assert (a + b) / b == q + 1 == a / b + 1;
}

lemma AbsProperty(s: int)
    requires s != 0
    ensures abs(s) > 0
    ensures abs(s) >= 1
{
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
    var s := sum(cards);
    if s == 0 {
        result := 0;
    } else {
        var absS := abs(s);
        result := (absS + x - 1) / x;
        
        AbsProperty(s);
        assert absS >= 1;
        DivisionProperty(absS, x);
        assert result >= 1;
    }
}
// </vc-code>

