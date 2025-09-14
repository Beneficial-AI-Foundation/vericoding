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
lemma CountBuyableGamesProperties(games: seq<int>, bills: seq<int>)
    requires forall i :: 0 <= i < |games| ==> games[i] >= 1
    requires forall i :: 0 <= i < |bills| ==> bills[i] >= 1
    ensures 0 <= countBuyableGames(games, bills) <= |games|
    ensures countBuyableGames(games, bills) <= |bills|
{
    if |games| == 0 {
    } else if |bills| == 0 {
    } else if bills[0] >= games[0] {
        CountBuyableGamesProperties(games[1..], bills[1..]);
    } else {
        CountBuyableGamesProperties(games[1..], bills);
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
    CountBuyableGamesProperties(games, bills);
    
    var g := games;
    var b := bills;
    result := 0;
    
    while |g| > 0 && |b| > 0
        invariant 0 <= |g| <= |games|
        invariant 0 <= |b| <= |bills|
        invariant forall i :: 0 <= i < |g| ==> g[i] >= 1
        invariant forall i :: 0 <= i < |b| ==> b[i] >= 1
        invariant result + countBuyableGames(g, b) == countBuyableGames(games, bills)
        invariant 0 <= result <= |games| - |g|
    {
        if b[0] >= g[0] {
            result := result + 1;
            g := g[1..];
            b := b[1..];
        } else {
            g := g[1..];
        }
    }
}
// </vc-code>

