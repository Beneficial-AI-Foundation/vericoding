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
lemma AdvCountsNonNegative(n: int, r: seq<int>, b: seq<int>)
    requires ValidInput(n, r, b)
    ensures RobotAdvantageCount(n, r, b) >= 0
    ensures OpponentAdvantageCount(n, r, b) >= 0
{
}

lemma DivisionLemma(a: int, b: int)
    requires a >= 0
    requires b > 0
    ensures a / b >= 0
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
  if !CanWin(n, r, b) {
    result := -1;
  } else {
    var robot := RobotAdvantageCount(n, r, b);
    var opponent := OpponentAdvantageCount(n, r, b);
    AdvCountsNonNegative(n, r, b);
    DivisionLemma(opponent, robot);
    result := opponent / robot + 1;
  }
}
// </vc-code>

