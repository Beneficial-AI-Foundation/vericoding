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
function IntToString(x: int): string {
    if x == 1 then "1"
    else if x == 2 then "2"
    else ""
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
    requires ValidInput(n)
    ensures ValidResult(n, result)
// </vc-spec>
// <vc-code>
{
  if n % 2 == 0 {
    var move := OptimalWhiteMove(n);
    return "white\n" + IntToString(move.0) + " " + IntToString(move.1) + "\n";
  } else {
    return "black\n";
  }
}
// </vc-code>

