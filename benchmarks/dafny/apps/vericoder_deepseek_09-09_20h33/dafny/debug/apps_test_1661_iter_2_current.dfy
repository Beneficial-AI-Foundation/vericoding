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

lemma countBuyableGamesLemma(games: seq<int>, bills: seq<int>, i: int, j: int)
    requires forall i :: 0 <= i < |games| ==> games[i] >= 1
    requires forall i :: 0 <= i < |bills| ==> bills[i] >= 1
    requires 0 <= i <= |games|
    requires 0 <= j <= |bills|
    ensures countBuyableGames(games, bills) == countBuyableGames(games[i..], bills[j..]) + countBuyableGames(games[0..i], bills[0..j])
    decreases |games| - i, |bills| - j
{
    if i == 0 && j == 0 {
        // Base case
    } else if i > 0 && j > 0 {
        if bills[j-1] >= games[i-1] {
            countBuyableGamesLemma(games, bills, i-1, j-1);
        } else {
            countBuyableGamesLemma(games, bills, i-1, j);
        }
    }
    // Handle other cases where i > 0, j == 0 or i == 0, j > 0
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
        
        // Add this assertion to help the verifier
        assert result == countBuyableGames(games[0..i], bills[0..j]);
    }
    
    // After the loop, we need to account for remaining games
    if i < |games| {
        countBuyableGamesLemma(games, bills, i, j);
        assert countBuyableGames(games, bills) == countBuyableGames(games[i..], bills[j..]) + result;
        assert countBuyableGames(games[i..], bills[j..]) == 0;  // No bills left to buy remaining games
    }
}
// </vc-code>

