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
function method ApplyMoves(initialPos: int, n: int): int
    requires n >= 0
    requires ValidPosition(initialPos)
    ensures ValidPosition(ApplyMoves(initialPos, n))
{
    if n == 0 then
        initialPos
    else
        SwapMove(ApplyMoves(initialPos, n - 1), n)
}

lemma lemma_apply_moves_is_shell_game(initialPos: int, n: int)
    requires n >= 0
    requires ValidPosition(initialPos)
    ensures ApplyMoves(initialPos, n) == ShellGame(n, initialPos)
    decreases n
{
    if n == 0 {
    } else {
        lemma_apply_moves_is_shell_game(initialPos, n - 1);
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
    result := ApplyMoves(x, n);
}
// </vc-code>

