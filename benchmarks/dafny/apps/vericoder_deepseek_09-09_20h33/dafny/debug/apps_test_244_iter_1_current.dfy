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

lemma LemmaCyclePeriodicity()
    ensures forall pos: int, n: int :: 
        ValidPosition(pos) && n >= 0 ==> 
        SwapMove(SwapMove(SwapMove(pos, 1), 2), 1) == pos
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
    var currentPos := x;
    var counter := n;
    
    while counter > 0
        invariant counter >= 0
        invariant ValidPosition(currentPos)
        decreases counter
    {
        if counter % 2 == 1 {
            currentPos := SwapMove(currentPos, counter);
        }
        counter := counter - 1;
    }
    
    result := currentPos;
}
// </vc-code>

