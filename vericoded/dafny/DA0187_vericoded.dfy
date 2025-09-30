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

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: string)
    requires ValidInput(n, m)
    ensures result == Winner(n, m)
    ensures result == "Akshat" || result == "Malvika"
// </vc-spec>
// <vc-code>
{
    var moves := if n < m then n else m;
    if moves % 2 == 1 {
        result := "Akshat";
    } else {
        result := "Malvika";
    }
}
// </vc-code>

