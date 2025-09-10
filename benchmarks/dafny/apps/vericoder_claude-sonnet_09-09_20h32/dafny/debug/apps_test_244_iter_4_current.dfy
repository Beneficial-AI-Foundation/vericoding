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
lemma SwapMoveInverse(pos: int, moveNum: int)
    requires ValidPosition(pos)
    requires moveNum >= 1
    ensures SwapMove(SwapMove(pos, moveNum), moveNum) == pos
{
    if moveNum % 2 == 1 {
        // Odd move: swap 0 and 1
        if pos == 0 {
            assert SwapMove(pos, moveNum) == 1;
            assert SwapMove(1, moveNum) == 0;
        } else if pos == 1 {
            assert SwapMove(pos, moveNum) == 0;
            assert SwapMove(0, moveNum) == 1;
        } else {
            assert pos == 2;
            assert SwapMove(pos, moveNum) == 2;
            assert SwapMove(2, moveNum) == 2;
        }
    } else {
        // Even move: swap 1 and 2
        if pos == 1 {
            assert SwapMove(pos, moveNum) == 2;
            assert SwapMove(2, moveNum) == 1;
        } else if pos == 2 {
            assert SwapMove(pos, moveNum) == 1;
            assert SwapMove(1, moveNum) == 2;
        } else {
            assert pos == 0;
            assert SwapMove(pos, moveNum) == 0;
            assert SwapMove(0, moveNum) == 0;
        }
    }
}

lemma SixMoveCycle(pos: int)
    requires ValidPosition(pos)
    ensures forall i :: 1 <= i <= 6 ==> ValidPosition(ApplyMoves(pos, i))
    ensures ApplyMoves(pos, 6) == pos
{
    // After 6 moves, we return to original position
}

function ApplyMoves(pos: int, numMoves: int): int
    requires ValidPosition(pos)
    requires numMoves >= 0
    ensures ValidPosition(ApplyMoves(pos, numMoves))
{
    if numMoves == 0 then pos
    else SwapMove(ApplyMoves(pos, numMoves - 1), numMoves)
}

lemma CycleLength6(pos: int)
    requires ValidPosition(pos)
    ensures ApplyMoves(pos, 6) == pos
{
    // The shell game has a cycle of length 6
    if pos == 0 {
        assert ApplyMoves(0, 1) == 1;  // odd: 0->1
        assert ApplyMoves(0, 2) == 2;  // even: 1->2
        assert ApplyMoves(0, 3) == 2;  // odd: 2->2
        assert ApplyMoves(0, 4) == 1;  // even: 2->1
        assert ApplyMoves(0, 5) == 0;  // odd: 1->0
        assert ApplyMoves(0, 6) == 0;  // even: 0->0
    } else if pos == 1 {
        assert ApplyMoves(1, 1) == 0;  // odd: 1->0
        assert ApplyMoves(1, 2) == 0;  // even: 0->0
        assert ApplyMoves(1, 3) == 1;  // odd: 0->1
        assert ApplyMoves(1, 4) == 2;  // even: 1->2
        assert ApplyMoves(1, 5) == 2;  // odd: 2->2
        assert ApplyMoves(1, 6) == 1;  // even: 2->1
    } else {
        assert pos == 2;
        assert ApplyMoves(2, 1) == 2;  // odd: 2->2
        assert ApplyMoves(2, 2) == 1;  // even: 2->1
        assert ApplyMoves(2, 3) == 0;  // odd: 1->0
        assert ApplyMoves(2, 4) == 0;  // even: 0->0
        assert ApplyMoves(2, 5) == 1;  // odd: 0->1
        assert ApplyMoves(2, 6) == 2;  // even: 1->2
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
    // Since the pattern repeats every 6 moves, we only need to consider n mod 6
    var effectiveMoves := n % 6;
    result := ApplyMoves(x, effectiveMoves);
}
// </vc-code>

