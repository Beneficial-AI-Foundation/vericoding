predicate ValidInput(n: int, r: seq<int>, b: seq<int>)
{
    n > 0 && |r| == n && |b| == n &&
    (forall i :: 0 <= i < n ==> r[i] == 0 || r[i] == 1) &&
    (forall i :: 0 <= i < n ==> b[i] == 0 || b[i] == 1)
}

function RobotAdvantageCount(n: int, r: seq<int>, b: seq<int>): int
    requires ValidInput(n, r, b)
{
    |set i | 0 <= i < n && r[i] == 1 && b[i] == 0|
}

function OpponentAdvantageCount(n: int, r: seq<int>, b: seq<int>): int
    requires ValidInput(n, r, b)
{
    |set i | 0 <= i < n && r[i] == 0 && b[i] == 1|
}

predicate CanWin(n: int, r: seq<int>, b: seq<int>)
    requires ValidInput(n, r, b)
{
    RobotAdvantageCount(n, r, b) > 0
}

function MinMaxPointValue(n: int, r: seq<int>, b: seq<int>): int
    requires ValidInput(n, r, b)
    requires CanWin(n, r, b)
{
    OpponentAdvantageCount(n, r, b) / RobotAdvantageCount(n, r, b) + 1
}

// <vc-helpers>
lemma RobotAdvantageCountCorrect(n: int, r: seq<int>, b: seq<int>)
    requires ValidInput(n, r, b)
    ensures RobotAdvantageCount(n, r, b) == |set i | 0 <= i < n && r[i] == 1 && b[i] == 0|
{
    var s := set i | 0 <= i < n && r[i] == 1 && b[i] == 0;
    assert RobotAdvantageCount(n, r, b) == |s|;
}

lemma OpponentAdvantageCountCorrect(n: int, r: seq<int>, b: seq<int>)
    requires ValidInput(n, r, b)
    ensures OpponentAdvantageCount(n, r, b) == |set i | 0 <= i < n && r[i] == 0 && b[i] == 1|
{
    var s := set i | 0 <= i < n && r[i] == 0 && b[i] == 1;
    assert OpponentAdvantageCount(n, r, b) == |s|;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, r: seq<int>, b: seq<int>) returns (result: int)
    requires ValidInput(n, r, b)
    ensures if CanWin(n, r, b) then result == MinMaxPointValue(n, r, b) else result == -1
// </vc-spec>
// <vc-code>
{
    var robotAdvantage := 0;
    var opponentAdvantage := 0;
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant robotAdvantage == |set j | 0 <= j < i && r[j] == 1 && b[j] == 0|
        invariant opponentAdvantage == |set j | 0 <= j < i && r[j] == 0 && b[j] == 1|
    {
        if r[i] == 1 && b[i] == 0 {
            robotAdvantage := robotAdvantage + 1;
        } else if r[i] == 0 && b[i] == 1 {
            opponentAdvantage := opponentAdvantage + 1;
        }
        i := i + 1;
    }
    
    assert robotAdvantage == RobotAdvantageCount(n, r, b);
    assert opponentAdvantage == OpponentAdvantageCount(n, r, b);
    
    if robotAdvantage > 0 {
        result := opponentAdvantage / robotAdvantage + 1;
        assert CanWin(n, r, b);
        assert result == MinMaxPointValue(n, r, b);
    } else {
        result := -1;
        assert !CanWin(n, r, b);
    }
}
// </vc-code>

