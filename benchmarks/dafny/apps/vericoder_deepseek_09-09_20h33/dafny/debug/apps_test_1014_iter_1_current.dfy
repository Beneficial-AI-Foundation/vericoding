predicate ValidInput(n: int) {
    n >= 2
}

predicate IsWinForWhite(n: int) {
    n % 2 == 0
}

predicate IsWinForBlack(n: int) {
    n % 2 == 1
}

function OptimalWhiteMove(n: int): (int, int)
    requires ValidInput(n)
    requires IsWinForWhite(n)
{
    (1, 2)
}

predicate ValidResult(n: int, result: string) 
    requires ValidInput(n)
{
    if IsWinForBlack(n) then
        result == "black\n"
    else
        result == "white\n1 2\n"
}

// <vc-helpers>
lemma WhiteWinEven(n: int)
    requires ValidInput(n) && IsWinForWhite(n)
    ensures n % 2 == 0
{
}

lemma BlackWinOdd(n: int)
    requires ValidInput(n) && IsWinForBlack(n)
    ensures n % 2 == 1
{
}

lemma WhiteWinImpliesEven(n: int)
    requires ValidInput(n)
    ensures IsWinForWhite(n) <==> n % 2 == 0
{
}

lemma BlackWinImpliesOdd(n: int)
    requires ValidInput(n)
    ensures IsWinForBlack(n) <==> n % 2 == 1
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
    requires ValidInput(n)
    ensures ValidResult(n, result)
// </vc-spec>
// <vc-code>
{
    if (n % 2 == 1) {
        result := "black\n";
    } else {
        result := "white\n1 2\n";
    }
}
// </vc-code>

