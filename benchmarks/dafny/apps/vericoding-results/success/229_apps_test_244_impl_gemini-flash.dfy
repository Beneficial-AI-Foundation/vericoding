// <vc-preamble>
predicate ValidPosition(pos: int) {
    0 <= pos <= 2
}

function SwapMove(pos: int, moveNum: int): int
    requires ValidPosition(pos)
    requires moveNum >= 1
    ensures ValidPosition(SwapMove(pos, moveNum))
{
    if moveNum % 2 == 1 then
        if pos == 0 then 1
        else if pos == 1 then 0
        else 2
    else
        if pos == 1 then 2
        else if pos == 2 then 1
        else 0
}

function ReverseMove(pos: int, moveNum: int): int
    requires ValidPosition(pos)
    requires moveNum >= 1
    ensures ValidPosition(ReverseMove(pos, moveNum))
{
    if moveNum % 2 == 1 then
        if pos == 0 then 1
        else if pos == 1 then 0
        else 2
    else
        if pos == 1 then 2
        else if pos == 2 then 1
        else 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax errors in if/else statements and variable declarations */
function ComputeFinalPosition(n: int, x: int): int
    requires n >= 0
    requires ValidPosition(x)
    ensures ValidPosition(ComputeFinalPosition(n, x))
    decreases n
{
    if n == 0 then (x)
    else if n % 2 == 1 then
        var prevPos := ComputeFinalPosition(n - 1, x);
        if prevPos == 0 then 1
        else if prevPos == 1 then 0
        else 2
    else
        var prevPos := ComputeFinalPosition(n - 1, x);
        if prevPos == 1 then 2
        else if prevPos == 2 then 1
        else 0
}
// </vc-helpers>

// <vc-spec>
method ShellGame(n: int, x: int) returns (result: int)
    requires n >= 1 && n <= 2000000000
    requires ValidPosition(x)
    ensures ValidPosition(result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes */
{
  result := ComputeFinalPosition(n, x);
}
// </vc-code>
