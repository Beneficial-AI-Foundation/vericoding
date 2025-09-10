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
lemma ParityProperty(n: int)
  ensures (n % 2 == 0 && n % 2 == 1) == false
{}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
    requires ValidInput(n)
    ensures ValidResult(n, result)
// </vc-spec>
// <vc-code>
{
    if IsWinForBlack(n) {
        result := "black\n";
    } else {
        assert IsWinForWhite(n); // follows from ParityProperty and definition of IsWinForBlack
        var move := OptimalWhiteMove(n);
        result := "white\n" + (move.0 as string) + " " + (move.1 as string) + "\n";
    }
}
// </vc-code>

