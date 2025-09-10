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
    else (if r[k-1] == 1 && b[k-1] == 0 then 1 else 0) + GhostRobotAdvantageCount(n, r, b, k - 1)
}

function GhostOpponentAdvantageCount(n: int, r: seq<int>, b: seq<int>, k: int): int
    requires 0 <= k <= n
    requires ValidInput(n, r, b)
    ensures GhostOpponentAdvantageCount(n, r, b, k) == |set i | 0 <= i < k && r[i] == 0 && b[i] == 1|
{
    if k == 0 then 0
    else (if r[k-1] == 0 && b[k-1] == 1 then 1 else 0) + GhostOpponentAdvantageCount(n, r, b, k - 1)
}

lemma RobotAdvantageCount_is_Ghost(n: int, r: seq<int>, b: seq<int>)
    requires ValidInput(n, r, b)
    ensures RobotAdvantageCount(n, r, b) == GhostRobotAdvantageCount(n, r, b, n)
{
    // The proof for the equivalence of RobotAdvantageCount and GhostRobotAdvantageCount(n,r,b,n)
    // is simply that GhostRobotAdvantageCount(n, r, b, n) by its ensures clause is
    // |set i | 0 <= i < n && r[i] == 1 && b[i] == 0|, which is the definition of RobotAdvantageCount.
}

lemma OpponentAdvantageCount_is_Ghost(n: int, r: seq<int>, b: seq<int>)
    requires ValidInput(n, r, b)
    ensures OpponentAdvantageCount(n, r, b) == GhostOpponentAdvantageCount(n, r, b, n)
{
    // Similar to RobotAdvantageCount_is_Ghost, the proof is implicit via the ensures clause.
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

    for i := 0 to n
        invariant 0 <= i <= n
        invariant robot_advantage == GhostRobotAdvantageCount(n, r, b, i)
        invariant opponent_advantage == GhostOpponentAdvantageCount(n, r, b, i)
    {
        if i < n { // Only access r[i] and b[i] if i is within bounds
            if r[i] == 1 && b[i] == 0 {
                robot_advantage := robot_advantage + 1;
            } else if r[i] == 0 && b[i] == 1 {
                opponent_advantage := opponent_advantage + 1;
            }
        }
    }

    // After the loop, robot_advantage and opponent_advantage hold values equivalent to
    // RobotAdvantageCount(n, r, b) and OpponentAdvantageCount(n, r, b) respectively,
    // due to the lemmas and loop invariants.
    // We explicitly refer to the defined functions for the postcondition.
    RobotAdvantageCount_is_Ghost(n, r, b);
    OpponentAdvantageCount_is_Ghost(n, r, b);
    GhostRobotAdvantageCount(n, r, b, n); // Calling the function to make its postcondition usable by the verifier
    GhostOpponentAdvantageCount(n, r, b, n); // Calling the function to make its postcondition usable by the verifier

    if robot_advantage > 0 {
        result := opponent_advantage / robot_advantage + 1;
    } else {
        result := -1;
    }
}
// </vc-code>

