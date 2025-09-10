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
    requires forall k :: 0 <= k < |games| ==> games[k] >= 1
    requires forall k :: 0 <= k < |bills| ==> bills[k] >= 1
    requires bills[j] >= games[i]
    ensures countBuyableGames(games[i..], bills[j..]) == 1 + countBuyableGames(games[i+1..], bills[j+1..])
{
    if i == |games| - 1 && j == |bills| - 1 {
        assert games[i..] == [games[i]];
        assert bills[j..] == [bills[j]];
        assert games[i+1..] == [];
        assert bills[j+1..] == [];
    } else {
        calc {
            countBuyableGames(games[i..], bills[j..]);
            ==
            if bills[j] >= games[i] then 
                1 + countBuyableGames(games[i+1..], bills[j+1..])
            else 
                countBuyableGames(games[i+1..], bills[j..]);
            ==
            if bills[j] >= games[i] then 
                1 + countBuyableGames(games[i+1..], bills[j+1..])
            else 
                1 + countBuyableGames(games[i+1..], bills[j+1..]);
            ==
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
    var i := 0;
    var j := 0;
    result := 0;
    
    while i < |games| && j < |bills|
        invariant 0 <= i <= |games| && 0 <= j <= |bills|
        invariant result + countBuyableGames(games[i..], bills[j..]) == countBuyableGames(games, bills)
        invariant 0 <= result <= i
        invariant result <= j
    {
        if bills[j] >= games[i] {
            result := result + 1;
            StepIfBuyable(games, bills, i, j);
            i := i + 1;
            j := j + 1;
        } else {
            i := i + 1;
        }
    }
    
    assert countBuyableGames(games[i..], bills[j..]) == 0;
}
// </vc-code>

