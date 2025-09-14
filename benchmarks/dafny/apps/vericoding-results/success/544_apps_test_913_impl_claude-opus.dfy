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
lemma SetComprehensionCount(n: int, r: seq<int>, b: seq<int>, robotAdv: int, oppAdv: int)
    requires ValidInput(n, r, b)
    requires robotAdv == |set i | 0 <= i < n && r[i] == 1 && b[i] == 0|
    requires oppAdv == |set i | 0 <= i < n && r[i] == 0 && b[i] == 1|
    ensures robotAdv == RobotAdvantageCount(n, r, b)
    ensures oppAdv == OpponentAdvantageCount(n, r, b)
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, r: seq<int>, b: seq<int>) returns (result: int)
    requires ValidInput(n, r, b)
    ensures if CanWin(n, r, b) then result == MinMaxPointValue(n, r, b) else result == -1
// </vc-spec>
// <vc-code>
{
    var robotAdvantages := 0;
    var opponentAdvantages := 0;
    var i := 0;
    
    var robotIndices := {};
    var oppIndices := {};
    
    while i < n
        invariant 0 <= i <= n
        invariant robotIndices == set j | 0 <= j < i && r[j] == 1 && b[j] == 0
        invariant oppIndices == set j | 0 <= j < i && r[j] == 0 && b[j] == 1
        invariant robotAdvantages == |robotIndices|
        invariant opponentAdvantages == |oppIndices|
    {
        if r[i] == 1 && b[i] == 0 {
            robotIndices := robotIndices + {i};
            robotAdvantages := robotAdvantages + 1;
        } else if r[i] == 0 && b[i] == 1 {
            oppIndices := oppIndices + {i};
            opponentAdvantages := opponentAdvantages + 1;
        }
        i := i + 1;
    }
    
    assert robotIndices == set j | 0 <= j < n && r[j] == 1 && b[j] == 0;
    assert oppIndices == set j | 0 <= j < n && r[j] == 0 && b[j] == 1;
    
    SetComprehensionCount(n, r, b, robotAdvantages, opponentAdvantages);
    
    if robotAdvantages > 0 {
        result := opponentAdvantages / robotAdvantages + 1;
        assert CanWin(n, r, b);
        assert result == MinMaxPointValue(n, r, b);
    } else {
        result := -1;
        assert !CanWin(n, r, b);
    }
}
// </vc-code>

