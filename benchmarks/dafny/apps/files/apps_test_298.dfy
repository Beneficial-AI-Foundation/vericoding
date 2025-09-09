Two players take turns removing exactly k consecutive sticks from either end of a row of n sticks.
The first player moves first. The game ends when fewer than k sticks remain.
Determine if the first player wins by making strictly more moves than the second player.

predicate ValidInput(n: int, k: int)
{
    k >= 1 && n >= 1 && k <= n
}

function TotalMoves(n: int, k: int): int
    requires ValidInput(n, k)
{
    n / k
}

predicate FirstPlayerWins(n: int, k: int)
    requires ValidInput(n, k)
{
    TotalMoves(n, k) % 2 == 1
}

method solve(n: int, k: int) returns (result: string)
    requires ValidInput(n, k)
    ensures FirstPlayerWins(n, k) ==> result == "YES"
    ensures !FirstPlayerWins(n, k) ==> result == "NO"
{
    var total_moves := TotalMoves(n, k);
    if total_moves % 2 == 1 {
        result := "YES";
    } else {
        result := "NO";
    }
}
