predicate ValidPosition(pos: int) {
    0 <= pos <= 2
}

function SwapMove(pos: int, moveNum: int): int
    requires ValidPosition(pos)
    requires moveNum >= 1
    ensures ValidPosition(SwapMove(pos, moveNum))
{
    if moveNum % 2 == 1 then // odd move: swap 0 and 1
        if pos == 0 then 1
        else if pos == 1 then 0
        else 2
    else // even move: swap 1 and 2
        if pos == 1 then 2
        else if pos == 2 then 1
        else 0
}

function ReverseMove(pos: int, moveNum: int): int
    requires ValidPosition(pos)
    requires moveNum >= 1
    ensures ValidPosition(ReverseMove(pos, moveNum))
{
    if moveNum % 2 == 1 then // reverse odd move: swap 0 and 1
        if pos == 0 then 1
        else if pos == 1 then 0
        else 2
    else // reverse even move: swap 1 and 2
        if pos == 1 then 2
        else if pos == 2 then 1
        else 0
}

// <vc-helpers>
lemma SwapCycle6(pos: int)
    requires ValidPosition(pos)
    ensures SwapMove(SwapMove(SwapMove(SwapMove(SwapMove(SwapMove(pos, 1), 2), 3), 4), 5), 6) == pos
{
    // Verify the 6-move cycle for each starting position
}

function ApplyMoves(pos: int, moveNum: int, count: int): int
    requires ValidPosition(pos)
    requires moveNum >= 1
    requires count >= 0
    ensures ValidPosition(ApplyMoves(pos, moveNum, count))
    decreases count
{
    if count == 0 then pos
    else ApplyMoves(SwapMove(pos, moveNum), moveNum + 1, count - 1)
}

lemma ApplyMovesCycle(pos: int, cycles: int)
    requires ValidPosition(pos)
    requires cycles >= 0
    ensures ApplyMoves(pos, 1, 6 * cycles) == pos
    decreases cycles
{
    if cycles == 0 {
        // Base case: 0 moves returns same position
    } else {
        // Inductive case: after 6 moves we're back at start
        assert ApplyMoves(pos, 1, 6) == pos by {
            SwapCycle6(pos);
        }
        ApplyMovesCycle(pos, cycles - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method ShellGame(n: int, x: int) returns (result: int)
    requires n >= 1 && n <= 2000000000
    requires ValidPosition(x)
    ensures ValidPosition(result)
// </vc-spec>
// <vc-code>
{
    var remainder := n % 6;
    
    if remainder == 0 {
        result := x;
    } else if remainder == 1 {
        result := SwapMove(x, 1);
    } else if remainder == 2 {
        result := SwapMove(SwapMove(x, 1), 2);
    } else if remainder == 3 {
        var temp := SwapMove(SwapMove(x, 1), 2);
        result := SwapMove(temp, 3);
    } else if remainder == 4 {
        var temp1 := SwapMove(SwapMove(x, 1), 2);
        var temp2 := SwapMove(temp1, 3);
        result := SwapMove(temp2, 4);
    } else { // remainder == 5
        var temp1 := SwapMove(SwapMove(x, 1), 2);
        var temp2 := SwapMove(temp1, 3);
        var temp3 := SwapMove(temp2, 4);
        result := SwapMove(temp3, 5);
    }
}
// </vc-code>

