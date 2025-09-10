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
function GhostRobotAdvantageCount(n: int, r: seq<int>, b: seq<int>, k: int): int
    requires 0 <= k <= n
    requires ValidInput(n, r, b)
    ensures GhostRobotAdvantageCount(n, r, b, k) == |set i | 0 <= i < k && r[i] == 1 && b[i] == 0|
{
    if k == 0 then 0
    else GhostRobotAdvantageCount(n, r, b, k - 1) + (if r[k-1] == 1 && b[k-1] == 0 then 1 else 0)
}

function GhostOpponentAdvantageCount(n: int, r: seq<int>, b: seq<int>, k: int): int
    requires 0 <= k <= n
    requires ValidInput(n, r, b)
    ensures GhostOpponentAdvantageCount(n, r, b, k) == |set i | 0 <= i < k && r[i] == 0 && b[i] == 1|
{
    if k == 0 then 0
    else GhostOpponentAdvantageCount(n, r, b, k - 1) + (if r[k-1] == 0 && b[k-1] == 1 then 1 else 0)
}

lemma RobotAdvantageCount_is_Ghost(n: int, r: seq<int>, b: seq<int>)
    requires ValidInput(n, r, b)
    ensures RobotAdvantageCount(n, r, b) == GhostRobotAdvantageCount(n, r, b, n)
{
    var count := 0;
    for i := 0 to n-1
        invariant 0 <= i <= n
        invariant count == GhostRobotAdvantageCount(n, r, b, i)
    {
        if r[i] == 1 && b[i] == 0 {
            count := count + 1;
        }
    }
    assert RobotAdvantageCount(n, r, b) == count;
}

lemma OpponentAdvantageCount_is_Ghost(n: int, r: seq<int>, b: seq<int>)
    requires ValidInput(n, r, b)
    ensures OpponentAdvantageCount(n, r, b) == GhostOpponentAdvantageCount(n, r, b, n)
{
    var count := 0;
    for i := 0 to n-1
        invariant 0 <= i <= n
        invariant count == GhostOpponentAdvantageCount(n, r, b, i)
    {
        if r[i] == 0 && b[i] == 1 {
            count := count + 1;
        }
    }
    assert OpponentAdvantageCount(n, r, b) == count;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, r: seq<int>, b: seq<int>) returns (result: int)
    requires ValidInput(n, r, b)
    ensures if CanWin(n, r, b) then result == MinMaxPointValue(n, r, b) else result == -1
// </vc-spec>
// <vc-code>
{
    var robot_advantage := 0;
    var opponent_advantage := 0;

    for i := 0 to n - 1
        invariant 0 <= i <= n
        invariant robot_advantage == GhostRobotAdvantageCount(n, r, b, i)
        invariant opponent_advantage == GhostOpponentAdvantageCount(n, r, b, i)
    {
        if r[i] == 1 && b[i] == 0 {
            robot_advantage := robot_advantage + 1;
        } else if r[i] == 0 && b[i] == 1 {
            opponent_advantage := opponent_advantage + 1;
        }
    }

    RobotAdvantageCount_is_Ghost(n, r, b);
    OpponentAdvantageCount_is_Ghost(n, r, b);

    if robot_advantage > 0 {
        result := opponent_advantage / robot_advantage + 1;
    } else {
        result := -1;
    }
}
// </vc-code>

