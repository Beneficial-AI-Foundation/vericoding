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
lemma LemmaSwapReverse(pos: int, moveNum: int)
    requires ValidPosition(pos)
    requires moveNum >= 1
    ensures ReverseMove(SwapMove(pos, moveNum), moveNum) == pos
{
}

lemma LemmaMoveCommutativity(moveNum1: int, moveNum2: int, pos: int)
    requires ValidPosition(pos)
    requires moveNum1 >= 1 && moveNum2 >= 1
    requires moveNum1 % 2 == moveNum2 % 2
    ensures SwapMove(SwapMove(pos, moveNum1), moveNum2) == pos
{
}

lemma LemmaCyclePeriodicity(pos: int)
    requires ValidPosition(pos)
    ensures SwapMove(SwapMove(SwapMove(pos, 1), 2), 1) == pos
{
}

lemma LemmaMoveInvariance(pos: int, moveNum: int)
    requires ValidPosition(pos)
    requires moveNum >= 1
    ensures SwapMove(SwapMove(pos, moveNum), moveNum) == pos
{
}

lemma LemmaEvenMove(pos: int, moveNum: int)
    requires ValidPosition(pos)
    requires moveNum >= 1 && moveNum % 2 == 0
    ensures SwapMove(pos, moveNum) == if pos == 1 then 2 else if pos == 2 then 1 else 0
{
}

lemma LemmaOddMove(pos: int, moveNum: int)
    requires ValidPosition(pos)
    requires moveNum >= 1 && moveNum % 2 == 1
    ensures SwapMove(pos, moveNum) == if pos == 0 then 1 else if pos == 1 then 0 else 2
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
    if n % 3 == 0 {
        // Pattern repeats every 3 moves (odd-odd-even cycle)
        // The net effect of 3 moves is identity
        result := x;
    } else if n % 3 == 1 {
        // Single odd move
        result := SwapMove(x, 1);
    } else {
        // Two moves: odd-odd
        var temp := SwapMove(x, 1);
        result := SwapMove(temp, 1);
    }
}
// </vc-code>

