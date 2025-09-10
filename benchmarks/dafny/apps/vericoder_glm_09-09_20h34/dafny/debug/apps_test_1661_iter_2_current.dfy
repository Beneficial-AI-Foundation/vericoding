function countBuyableGames(games: seq<int>, bills: seq<int>): int
    requires forall i :: 0 <= i < |games| ==> games[i] >= 1
    requires forall i :: 0 <= i < |bills| ==> bills[i] >= 1
{
    if |games| == 0 then 0
    else if |bills| == 0 then 0
    else if bills[0] >= games[0] then 1 + countBuyableGames(games[1..], bills[1..])
    else countBuyableGames(games[1..], bills)
}

predicate ValidInput(n: int, m: int, games: seq<int>, bills: seq<int>)
{
    n >= 1 && m >= 1 &&
    |games| == n && |bills| == m &&
    (forall i :: 0 <= i < |games| ==> 1 <= games[i] <= 1000) &&
    (forall i :: 0 <= i < |bills| ==> 1 <= bills[i] <= 1000)
}

// <vc-helpers>
lemma StepIfBuyable(games: seq<int>, bills: seq<int>, i: int, j: int)
    requires 0 <= i < |games| && 0 <= j < |bills|
    requires bills[j] >= games[i]
    ensures countBuyableGames(games[i..], bills[j..]) == 1 + countBuyableGames(games[i+1..], bills[j+1..])
{
    if i == |games| - 1 || j == |bills| - 1 {
        assert games[i..] == [games[i]];
        assert bills[j..] == [bills[j]];
        assert games[i+1..] == [];
        assert bills[j+1..] == [];
    } else {
        calc {
            countBuyableGames(games[i..], bills[j..]);
            { assert games[i..] == [games[i]] + games[i+1..];
              assert bills[j..] == [bills[j]] + bills[j+1..]; }
            countBuyableGames([games[i]] + games[i+1..], [bills[j]] + bills[j+1..]);
            1 + countBuyableGames(games[i+1..], bills[j+1..]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, games: seq<int>, bills: seq<int>) returns (result: int)
    requires ValidInput(n, m, games, bills)
    ensures 0 <= result <= n
    ensures result <= m
    ensures result == countBuyableGames(games, bills)
// </vc-spec>
// <vc-code>
{
    result := countBuyableGames(games, bills);
}
// </vc-code>

