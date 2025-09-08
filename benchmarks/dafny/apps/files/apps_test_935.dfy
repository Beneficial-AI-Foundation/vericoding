Given a grid with n horizontal and m vertical sticks, two players take turns
removing intersection points. When an intersection is removed, all sticks 
passing through it are removed. The player who cannot make a move loses.
Akshat goes first. Determine the winner when both players play optimally.

predicate ValidInput(n: int, m: int)
{
    1 <= n <= 100 && 1 <= m <= 100
}

function GameMoves(n: int, m: int): int
    requires ValidInput(n, m)
{
    if n < m then n else m
}

function Winner(n: int, m: int): string
    requires ValidInput(n, m)
{
    var moves := GameMoves(n, m);
    if moves % 2 == 1 then "Akshat" else "Malvika"
}

method solve(n: int, m: int) returns (result: string)
    requires ValidInput(n, m)
    ensures result == Winner(n, m)
    ensures result == "Akshat" || result == "Malvika"
{
    var minVal := if n < m then n else m;
    if minVal % 2 == 0 {
        result := "Malvika";
    } else {
        result := "Akshat";
    }
}
