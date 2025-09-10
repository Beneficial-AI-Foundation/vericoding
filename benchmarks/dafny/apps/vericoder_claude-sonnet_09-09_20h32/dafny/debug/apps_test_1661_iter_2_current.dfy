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
lemma countBuyableGamesProperties(games: seq<int>, bills: seq<int>)
    requires forall i :: 0 <= i < |games| ==> games[i] >= 1
    requires forall i :: 0 <= i < |bills| ==> bills[i] >= 1
    ensures countBuyableGames(games, bills) >= 0
    ensures countBuyableGames(games, bills) <= |games|
    ensures countBuyableGames(games, bills) <= |bills|
{
    if |games| == 0 {
    } else if |bills| == 0 {
    } else if bills[0] >= games[0] {
        countBuyableGamesProperties(games[1..], bills[1..]);
    } else {
        countBuyableGamesProperties(games[1..], bills);
    }
}

lemma countBuyableGamesIterative(games: seq<int>, bills: seq<int>, i: int, j: int)
    requires forall k :: 0 <= k < |games| ==> games[k] >= 1
    requires forall k :: 0 <= k < |bills| ==> bills[k] >= 1
    requires 0 <= i <= |games|
    requires 0 <= j <= |bills|
    ensures countBuyableGames(games[i..], bills[j..]) >= 0
    ensures countBuyableGames(games[i..], bills[j..]) <= |games| - i
    ensures countBuyableGames(games[i..], bills[j..]) <= |bills| - j
    decreases |games| - i + |bills| - j
{
    if i == |games| {
    } else if j == |bills| {
    } else if bills[j] >= games[i] {
        countBuyableGamesIterative(games, bills, i + 1, j + 1);
    } else {
        countBuyableGamesIterative(games, bills, i + 1, j);
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
    countBuyableGamesProperties(games, bills);
    
    var i := 0;
    var j := 0;
    var count := 0;
    
    while i < n && j < m
        invariant 0 <= i <= n
        invariant 0 <= j <= m
        invariant 0 <= count
        invariant count <= i
        invariant count <= j
        invariant count + countBuyableGames(games[i..], bills[j..]) == countBuyableGames(games, bills)
    {
        countBuyableGamesIterative(games, bills, i, j);
        
        if bills[j] >= games[i] {
            count := count + 1;
            i := i + 1;
            j := j + 1;
        } else {
            i := i + 1;
        }
    }
    
    result := count;
}
// </vc-code>

