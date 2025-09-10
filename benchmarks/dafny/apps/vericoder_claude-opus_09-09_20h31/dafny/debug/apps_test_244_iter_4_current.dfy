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
        assert ApplyMoves(pos, 1, 0) == pos;
    } else {
        // First prove that 6 moves from pos returns to pos
        calc == {
            ApplyMoves(pos, 1, 6);
            ApplyMoves(SwapMove(pos, 1), 2, 5);
            ApplyMoves(SwapMove(SwapMove(pos, 1), 2), 3, 4);
            ApplyMoves(SwapMove(SwapMove(SwapMove(pos, 1), 2), 3), 4, 3);
            ApplyMoves(SwapMove(SwapMove(SwapMove(SwapMove(pos, 1), 2), 3), 4), 5, 2);
            ApplyMoves(SwapMove(SwapMove(SwapMove(SwapMove(SwapMove(pos, 1), 2), 3), 4), 5), 6, 1);
            ApplyMoves(SwapMove(SwapMove(SwapMove(SwapMove(SwapMove(SwapMove(pos, 1), 2), 3), 4), 5), 6), 7, 0);
            SwapMove(SwapMove(SwapMove(SwapMove(SwapMove(SwapMove(pos, 1), 2), 3), 4), 5), 6);
            { SwapCycle6(pos); }
            pos;
        }
        
        // Now prove the full cycles case
        calc == {
            ApplyMoves(pos, 1, 6 * cycles);
            ApplyMoves(pos, 1, 6 + 6 * (cycles - 1));
            { ApplyMovesDecomposition(pos, 1, 6, 6 * (cycles - 1)); }
            ApplyMoves(ApplyMoves(pos, 1, 6), 7, 6 * (cycles - 1));
            { assert ApplyMoves(pos, 1, 6) == pos; }
            ApplyMoves(pos, 7, 6 * (cycles - 1));
            { ApplyMovesStartOffset(pos, 7, 1, 6 * (cycles - 1)); }
            ApplyMoves(pos, 1, 6 * (cycles - 1));
            { ApplyMovesCycle(pos, cycles - 1); }
            pos;
        }
    }
}

lemma ApplyMovesDecomposition(pos: int, moveNum: int, k: int, m: int)
    requires ValidPosition(pos)
    requires moveNum >= 1
    requires k >= 0 && m >= 0
    ensures ApplyMoves(pos, moveNum, k + m) == ApplyMoves(ApplyMoves(pos, moveNum, k), moveNum + k, m)
    decreases k
{
    if k == 0 {
        assert ApplyMoves(pos, moveNum, m) == ApplyMoves(ApplyMoves(pos, moveNum, 0), moveNum, m);
    } else {
        calc == {
            ApplyMoves(pos, moveNum, k + m);
            ApplyMoves(SwapMove(pos, moveNum), moveNum + 1, k - 1 + m);
            { ApplyMovesDecomposition(SwapMove(pos, moveNum), moveNum + 1, k - 1, m); }
            ApplyMoves(ApplyMoves(SwapMove(pos, moveNum), moveNum + 1, k - 1), moveNum + k, m);
            ApplyMoves(ApplyMoves(pos, moveNum, k), moveNum + k, m);
        }
    }
}

lemma ApplyMovesStartOffset(pos: int, startMove: int, targetMove: int, count: int)
    requires ValidPosition(pos)
    requires startMove >= 1 && targetMove >= 1
    requires count >= 0
    requires (startMove - targetMove) % 6 == 0
    ensures ApplyMoves(pos, startMove, count) == ApplyMoves(pos, targetMove, count)
    decreases count
{
    if count == 0 {
        assert ApplyMoves(pos, startMove, 0) == pos == ApplyMoves(pos, targetMove, 0);
    } else {
        var diff := startMove - targetMove;
        assert diff % 6 == 0;
        
        // The key insight: moves repeat with period 6
        assert SwapMove(pos, startMove) == SwapMove(pos, targetMove) by {
            if startMove % 2 == targetMove % 2 {
                // Same parity means same swap operation
            }
        }
        
        ApplyMovesStartOffset(SwapMove(pos, startMove), startMove + 1, targetMove + 1, count - 1);
    }
}

lemma ApplyMovesModulo(pos: int, n: int)
    requires ValidPosition(pos)
    requires n >= 1
    ensures ApplyMoves(pos, 1, n) == ApplyMoves(pos, 1, n % 6)
{
    var cycles := n / 6;
    var remainder := n % 6;
    
    assert n == 6 * cycles + remainder;
    
    if cycles == 0 {
        assert n == remainder;
        assert ApplyMoves(pos, 1, n) == ApplyMoves(pos, 1, remainder);
    } else {
        calc == {
            ApplyMoves(pos, 1, n);
            ApplyMoves(pos, 1, 6 * cycles + remainder);
            { ApplyMovesDecomposition(pos, 1, 6 * cycles, remainder); }
            ApplyMoves(ApplyMoves(pos, 1, 6 * cycles), 6 * cycles + 1, remainder);
            { ApplyMovesCycle(pos, cycles); }
            ApplyMoves(pos, 6 * cycles + 1, remainder);
            { ApplyMovesStartOffset(pos, 6 * cycles + 1, 1, remainder); }
            ApplyMoves(pos, 1, remainder);
            ApplyMoves(pos, 1, n % 6);
        }
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
    
    ApplyMovesModulo(x, n);
    assert ApplyMoves(x, 1, n) == ApplyMoves(x, 1, remainder);
    
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
    
    assert result == ApplyMoves(x, 1, remainder);
}
// </vc-code>

