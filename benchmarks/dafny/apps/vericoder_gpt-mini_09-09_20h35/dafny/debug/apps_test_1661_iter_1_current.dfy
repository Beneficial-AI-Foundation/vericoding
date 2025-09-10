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
lemma CountBuyableBounds(games: seq<int>, bills: seq<int>)
    requires forall i :: 0 <= i < |games| ==> games[i] >= 1
    requires forall i :: 0 <= i < |bills| ==> bills[i] >= 1
    ensures 0 <= countBuyableGames(games, bills) <= |games|
    ensures countBuyableGames(games, bills) <= |bills|
    decreases |games| + |bills|
{
    if |games| == 0 || |bills| == 0 {
        // By definition countBuyableGames returns 0 in these cases
        assert countBuyableGames(games, bills) == 0;
        assert 0 <= countBuyableGames(games, bills);
        assert countBuyableGames(games, bills) <= |games|;
        assert countBuyableGames(games, bills) <= |bills|;
    } else {
        // both lengths >= 1
        if bills[0] >= games[0] {
            // countBuyableGames(games, bills) == 1 + countBuyableGames(games[1..], bills[1..])
            CountBuyableBounds(games[1..], bills[1..]);
            assert 0 <= countBuyableGames(games[1..], bills[1..]);
            assert countBuyableGames(games, bills) == 1 + countBuyableGames(games[1..], bills[1..]);
            // |games[1..]| == |games| - 1 and |bills[1..]| == |bills| - 1
            assert |games[1..]| == |games| - 1;
            assert |bills[1..]| == |bills| - 1;
            // therefore
            assert countBuyableGames(games, bills) <= 1 + |games[1..]|;
            assert countBuyableGames(games, bills) <= 1 + |bills[1..]|;
            assert 1 + |games[1..]| == |games|;
            assert 1 + |bills[1..]| == |bills|;
            assert countBuyableGames(games, bills) <= |games|;
            assert countBuyableGames(games, bills) <= |bills|;
            assert 0 <= countBuyableGames(games, bills);
        } else {
            // countBuyableGames(games, bills) == countBuyableGames(games[1..], bills)
            CountBuyableBounds(games[1..], bills);
            assert countBuyableGames(games, bills) == countBuyableGames(games[1..], bills);
            assert 0 <= countBuyableGames(games[1..], bills);
            // |games[1..]| == |games| - 1
            assert |games[1..]| == |games| - 1;
            assert countBuyableGames(games, bills) <= |games[1..]|;
            assert countBuyableGames(games, bills) <= |bills|;
            assert countBuyableGames(games, bills) <= |games|;
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
  CountBuyableBounds(games, bills);
}
// </vc-code>

