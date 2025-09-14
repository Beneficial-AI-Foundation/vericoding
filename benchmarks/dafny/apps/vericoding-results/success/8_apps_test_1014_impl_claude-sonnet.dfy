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
lemma EvenOddPartition(n: int)
    requires n >= 2
    ensures IsWinForWhite(n) || IsWinForBlack(n)
    ensures !(IsWinForWhite(n) && IsWinForBlack(n))
{
}

lemma ValidResultForBlack(n: int)
    requires ValidInput(n)
    requires IsWinForBlack(n)
    ensures ValidResult(n, "black\n")
{
}

lemma ValidResultForWhite(n: int)
    requires ValidInput(n)
    requires IsWinForWhite(n)
    ensures ValidResult(n, "white\n1 2\n")
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
    EvenOddPartition(n);
    if IsWinForBlack(n) {
        ValidResultForBlack(n);
        result := "black\n";
    } else {
        ValidResultForWhite(n);
        result := "white\n1 2\n";
    }
}
// </vc-code>

