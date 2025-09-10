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
        assert games[0..0] == [] && bills[0..0] == [];
        assert countBuyableGames(games[0..0], bills[0..0]) == 0;
    } else if i > 0 && j > 0 {
        if bills[j-1] >= games[i-1] {
            countBuyableGamesLemma(games, bills, i-1, j-1);
            var g1 := games[0..i-1];
            var b1 := bills[0..j-1];
            var g2 := games[i-1..];
            var b2 := bills[j-1..];
            assert games[0..i] == g1 + [games[i-1]];
            assert bills[0..j] == b1 + [bills[j-1]];
            assert games[i..] == g2[1..];
            assert bills[j..] == b2[1..];
        } else {
            countBuyableGamesLemma(games, bills, i-1, j);
            var g1 := games[0..i-1];
            var b1 := bills[0..j];
            assert games[0..i] == g1 + [games[i-1]];
            assert bills[0..j] == b1;
        }
    } else if i > 0 {
        countBuyableGamesLemma(games, bills, i-1, j);
        var g1 := games[0..i-1];
        assert games[0..i] == g1 + [games[i-1]];
    } else if j > 0 {
        countBuyableGamesLemma(games, bills, i, j-1);
        var b1 := bills[0..j-1];
        assert bills[0..j] == b1 + [bills[j-1]];
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
    
    // Use the lemma to relate the result to the complete count
    countBuyableGamesLemma(games, bills, i, j);
    assert countBuyableGames(games, bills) == countBuyableGames(games[i..], bills[j..]) + result;
    
    // Prove that no more games can be bought with remaining bills
    if j < |bills| {
        // Some bills remain, but no games
    } else {
        // No bills remain, so remaining games can't be bought
        countBuyableGamesIsMinLength(games[i..], bills[j..]);
        assert countBuyableGames(games[i..], bills[j..]) == 0;
    }
}
// </vc-code>

