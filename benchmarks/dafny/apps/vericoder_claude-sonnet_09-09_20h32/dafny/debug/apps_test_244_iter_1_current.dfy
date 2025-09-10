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
}

lemma TwoMoveCycle(pos: int, moveNum: int)
    requires ValidPosition(pos)
    requires moveNum >= 1
    ensures SwapMove(SwapMove(pos, moveNum), moveNum + 1) == SwapMove(SwapMove(pos, moveNum + 1), moveNum)
{
}

lemma FourMoveCycle(pos: int)
    requires ValidPosition(pos)
    ensures SwapMove(SwapMove(SwapMove(SwapMove(pos, 1), 2), 3), 4) == pos
{
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
    var current := x;
    var moves := n % 4;
    var i := 0;
    
    while i < moves
        invariant 0 <= i <= moves
        invariant ValidPosition(current)
    {
        current := SwapMove(current, (i % 2) + 1);
        i := i + 1;
    }
    
    result := current;
}
// </vc-code>

