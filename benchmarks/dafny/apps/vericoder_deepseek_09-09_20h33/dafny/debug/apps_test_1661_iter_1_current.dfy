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
lemma countBuyableGamesIsMinLength(games: seq<int>, bills: seq<int>)
    requires forall i :: 0 <= i < |games| ==> games[i] >= 1
    requires forall i :: 0 <= i < |bills| ==> bills[i] >= 1
    ensures countBuyableGames(games, bills) <= |games|
    ensures countBuyableGames(games, bills) <= |bills|
    decreases |games|, |bills|
{
    if |games| == 0 || |bills| == 0 {
        // Base case: result is 0, which is <= both lengths
    } else {
        if bills[0] >= games[0] {
            countBuyableGamesIsMinLength(games[1..], bills[1..]);
        } else {
            countBuyableGamesIsMinLength(games[1..], bills);
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
    var i := 0;
    var j := 0;
    result := 0;
    
    while i < |games| && j < |bills|
        invariant 0 <= i <= |games|
        invariant 0 <= j <= |bills|
        invariant 0 <= result <= i
        invariant result <= j
        invariant result == countBuyableGames(games[0..i], bills[0..j])
    {
        if bills[j] >= games[i] {
            result := result + 1;
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

