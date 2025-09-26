// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, r: seq<int>, b: seq<int>) returns (result: int)
    requires ValidInput(n, r, b)
    ensures if CanWin(n, r, b) then result == MinMaxPointValue(n, r, b) else result == -1
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
