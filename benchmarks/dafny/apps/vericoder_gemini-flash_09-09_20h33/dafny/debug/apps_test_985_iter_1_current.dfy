predicate ValidInput(positions: seq<(int, int)>)
{
    |positions| >= 1 && |positions| <= 200000 &&
    (forall i :: 0 <= i < |positions| ==> 
        1 <= positions[i].0 <= 1000 && 1 <= positions[i].1 <= 1000) &&
    (forall i, j :: 0 <= i < j < |positions| ==> positions[i] != positions[j])
}

function CountAttackingPairs(positions: seq<(int, int)>): int
    requires ValidInput(positions)
{
    |set i, j | 0 <= i < j < |positions| && 
               (positions[i].0 + positions[i].1 == positions[j].0 + positions[j].1 ||
                positions[i].0 - positions[i].1 == positions[j].0 - positions[j].1) :: (i, j)|
}

predicate ValidOutput(positions: seq<(int, int)>, result: int)
    requires ValidInput(positions)
{
    result == CountAttackingPairs(positions) && result >= 0
}

// <vc-helpers>
function CountAttacksOnDiagonal(count: map<int, int>): int
    reads count
    ensures CountAttacksOnDiagonal(count) >= 0
{
    var sum := 0;
    for value := range count.Values {
        sum := sum + value * (value - 1) / 2;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
method SolveBishops(positions: seq<(int, int)>) returns (result: int)
    requires ValidInput(positions)
    ensures ValidOutput(positions, result)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var primaryDiagonals: map<int, int> := map[];
    var secondaryDiagonals: map<int, int> := map[];

    for i := 0 to |positions| - 1
        invariant 0 <= i <= |positions|
        invariant forall k :: 0 <= k < i ==> primaryDiagonals.Contains(positions[k].0 + positions[k].1)
        invariant forall k :: 0 <= k < i ==> secondaryDiagonals.Contains(positions[k].0 - positions[k].1)
        invariant forall k :: primaryDiagonals.Contains(k) ==> primaryDiagonals[k] >= 0
        invariant forall k :: secondaryDiagonals.Contains(k) ==> secondaryDiagonals[k] >= 0
    {
        var x := positions[i].0;
        var y := positions[i].1;

        var primaryDiagonalSum := x + y;
        var secondaryDiagonalSum := x - y;

        if primaryDiagonals.Contains(primaryDiagonalSum) {
            primaryDiagonals := primaryDiagonals := primaryDiagonals[primaryDiagonalSum := primaryDiagonals[primaryDiagonalSum] + 1];
        } else {
            primaryDiagonals := primaryDiagonals := primaryDiagonals[primaryDiagonalSum := 1];
        }

        if secondaryDiagonals.Contains(secondaryDiagonalSum) {
            secondaryDiagonals := secondaryDiagonals := secondaryDiagonals[secondaryDiagonalSum := secondaryDiagonals[secondaryDiagonalSum] + 1];
        } else {
            secondaryDiagonals := secondaryDiagonals := secondaryDiagonals[secondaryDiagonalSum := 1];
        }
    }

    result := CountAttacksOnDiagonal(primaryDiagonals) + CountAttacksOnDiagonal(secondaryDiagonals);
}
// </vc-code>

