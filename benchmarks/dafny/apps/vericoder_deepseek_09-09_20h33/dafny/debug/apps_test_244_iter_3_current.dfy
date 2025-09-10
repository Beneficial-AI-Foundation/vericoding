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
    if moveNum % 2 == 1 {
        // Odd move: 0↔1
        assert (pos == 0 ==> ReverseMove(SwapMove(pos, moveNum), moveNum) == ReverseMove(1, moveNum) == 0);
        assert (pos == 1 ==> ReverseMove(SwapMove(pos, moveNum), moveNum) == ReverseMove(0, moveNum) == 1);
        assert (pos == 2 ==> ReverseMove(SwapMove(pos, moveNum), moveNum) == ReverseMove(2, moveNum) == 2);
    } else {
        // Even move: 1↔2
        assert (pos == 0 ==> ReverseMove(SwapMove(pos, moveNum), moveNum) == ReverseMove(0, moveNum) == 0);
        assert (pos == 1 ==> ReverseMove(SwapMove(pos, moveNum), moveNum) == ReverseMove(2, moveNum) == 1);
        assert (pos == 2 ==> ReverseMove(SwapMove(pos, moveNum), moveNum) == ReverseMove(1, moveNum) == 2);
    }
}

lemma LemmaMoveCommutativity(moveNum1: int, moveNum2: int, pos: int)
    requires ValidPosition(pos)
    requires moveNum1 >= 1 && moveNum2 >= 1
    requires moveNum1 % 2 == moveNum2 % 2
    ensures SwapMove(SwapMove(pos, moveNum1), moveNum2) == pos
{
    if moveNum1 % 2 == 1 {
        // Both odd moves: 0↔1
        if pos == 0 {
            assert SwapMove(SwapMove(0, moveNum1), moveNum2) == SwapMove(1, moveNum2) == 0;
        } else if pos == 1 {
            assert SwapMove(SwapMove(1, moveNum1), moveNum2) == SwapMove(0, moveNum2) == 1;
        } else {
            assert SwapMove(SwapMove(2, moveNum1), moveNum2) == SwapMove(2, moveNum2) == 2;
        }
    } else {
        // Both even moves: 1↔2
        if pos == 0 {
            assert SwapMove(SwapMove(0, moveNum1), moveNum2) == SwapMove(0, moveNum2) == 0;
        } else if pos == 1 {
            assert SwapMove(SwapMove(1, moveNum1), moveNum2) == SwapMove(2, moveNum2) == 1;
        } else {
            assert SwapMove(SwapMove(2, moveNum1), moveNum2) == SwapMove(1, moveNum2) == 2;
        }
    }
}

lemma LemmaCyclePeriodicity(pos: int)
    requires ValidPosition(pos)
    ensures SwapMove(SwapMove(SwapMove(pos, 1), 2), 1) == pos
{
    match pos {
        case 0 =>
            assert SwapMove(SwapMove(SwapMove(0, 1), 2), 1) == SwapMove(SwapMove(1, 2), 1) == SwapMove(2, 1) == 0;
        case 1 =>
            assert SwapMove(SwapMove(SwapMove(1, 1), 2), 1) == SwapMove(SwapMove(0, 2), 1) == SwapMove(0, 1) == 1;
        case 2 =>
            assert SwapMove(SwapMove(SwapMove(2, 1), 2), 1) == SwapMove(SwapMove(2, 2), 1) == SwapMove(1, 1) == 2;
    }
}

lemma LemmaMoveInvariance(pos: int, moveNum: int)
    requires ValidPosition(pos)
    requires moveNum >= 1
    ensures SwapMove(SwapMove(pos, moveNum), moveNum) == pos
{
    if moveNum % 2 == 1 {
        // Odd move: 0↔1
        if pos == 0 {
            assert SwapMove(SwapMove(0, moveNum), moveNum) == SwapMove(1, moveNum) == 0;
        } else if pos == 1 {
            assert SwapMove(SwapMove(1, moveNum), moveNum) == SwapMove(0, moveNum) == 1;
        } else {
            assert SwapMove(SwapMove(2, moveNum), moveNum) == SwapMove(2, moveNum) == 2;
        }
    } else {
        // Even move: 1↔2
        if pos == 0 {
            assert SwapMove(SwapMove(0, moveNum), moveNum) == SwapMove(0, moveNum) == 0;
        } else if pos == 1 {
            assert SwapMove(SwapMove(1, moveNum), moveNum) == SwapMove(2, moveNum) == 1;
        } else {
            assert SwapMove(SwapMove(2, moveNum), moveNum) == SwapMove(1, moveNum) == 2;
        }
    }
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
        result := x;
    } else if n % 3 == 1 {
        result := SwapMove(x, 1);
    } else {
        // n % 3 == 2: odd-odd-even pattern
        var temp1 := SwapMove(x, 1);
        var temp2 := SwapMove(temp1, 1);
        result := SwapMove(temp2, 2);
        LemmaMoveInvariance(x, 1);
        LemmaMoveCommutativity(1, 1, x);
        LemmaCyclePeriodicity(x);
    }
}
// </vc-code>

