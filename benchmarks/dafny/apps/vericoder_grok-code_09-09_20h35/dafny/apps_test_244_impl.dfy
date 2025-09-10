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
// no changes needed
// </vc-helpers>

// <vc-spec>
method ShellGame(n: int, x: int) returns (result: int)
    requires n >= 1 && n <= 2000000000
    requires ValidPosition(x)
    ensures ValidPosition(result)
// </vc-spec>
// <vc-code>
{
    var pos := x;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant ValidPosition(pos)
    {
        pos := SwapMove(pos, i);
        i := i + 1;
    }
    result := pos;
}
// </vc-code>

