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
function CountBuyableGamesIteration(games: seq<int>, bills: seq<int>, gameIndex: int, billIndex: int): int
    requires 0 <= gameIndex <= |games|
    requires 0 <= billIndex <= |bills|
    requires forall i :: 0 <= i < |games| ==> games[i] >= 1
    requires forall i :: 0 <= i < |bills| ==> bills[i] >= 1
    decreases (|games| - gameIndex) + (|bills| - billIndex)
{
    if gameIndex == |games| then 0
    else if billIndex == |bills| then 0
    else if bills[billIndex] >= games[gameIndex] then
        1 + CountBuyableGamesIteration(games, bills, gameIndex + 1, billIndex + 1)
    else
        CountBuyableGamesIteration(games, bills, gameIndex + 1, billIndex)
}

lemma lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games: seq<int>, bills: seq<int>, gameIndex: int, billIndex: int)
    returns (result: int)
    requires 0 <= gameIndex <= |games|
    requires 0 <= billIndex <= |bills|
    requires forall i :: 0 <= i < |games| ==> games[i] >= 1
    requires forall i :: 0 <= i < |bills| ==> bills[i] >= 1
    ensures CountBuyableGamesIteration(games, bills, gameIndex, billIndex) == countBuyableGames(games[gameIndex..], bills[billIndex..])
    decreases (|games| - gameIndex) + (|bills| - billIndex)
{
    if gameIndex == |games| then
        result := CountBuyableGamesIteration(games, bills, gameIndex, billIndex);
    else if billIndex == |bills| then
        result := CountBuyableGamesIteration(games, bills, gameIndex, billIndex);
    else if bills[billIndex] >= games[gameIndex] then {
        var _ := lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games, bills, gameIndex + 1, billIndex + 1);
        Calc {
            CountBuyableGamesIteration(games, bills, gameIndex, billIndex);
            1 + CountBuyableGamesIteration(games, bills, gameIndex + 1, billIndex + 1);
            { lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games, bills, gameIndex + 1, billIndex + 1); }
            1 + countBuyableGames(games[gameIndex + 1 ..], bills[billIndex + 1 ..]);
            countBuyableGames(games[gameIndex .. ], bills[billIndex .. ]);
        }
        result := CountBuyableGamesIteration(games, bills, gameIndex, billIndex);
    } else {
        var _ := lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games, bills, gameIndex + 1, billIndex);
        Calc {
            CountBuyableGamesIteration(games, bills, gameIndex, billIndex);
            CountBuyableGamesIteration(games, bills, gameIndex + 1, billIndex);
            { lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games, bills, gameIndex + 1, billIndex); }
            countBuyableGames(games[gameIndex + 1 ..], bills[billIndex .. ]);
            countBuyableGames(games[gameIndex .. ], bills[billIndex .. ]);
        }
        result := CountBuyableGamesIteration(games, bills, gameIndex, billIndex);
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
    var gameIndex := 0;
    var billIndex := 0;
    result := 0;

    lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games, bills, 0, 0);

    while gameIndex < n
        invariant 0 <= gameIndex <= n
        invariant 0 <= billIndex <= m
        invariant countBuyableGames(games, bills) ==
                  result + CountBuyableGamesIteration(games, bills, gameIndex, billIndex)
        invariant forall i :: 0 <= i < |games| ==> games[i] >= 1
        invariant forall i :: 0 <= i < |bills| ==> bills[i] >= 1
        invariant CountBuyableGamesIteration(games, bills, gameIndex, billIndex) == countBuyableGames(games[gameIndex..], bills[billIndex..])
        decreases n - gameIndex
    {
        if billIndex < m {
            if bills[billIndex] >= games[gameIndex] {
                lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games, bills, gameIndex + 1, billIndex + 1);
                result := result + 1;
                billIndex := billIndex + 1;
                gameIndex := gameIndex + 1;
            } else {
                lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games, bills, gameIndex + 1, billIndex);
                gameIndex := gameIndex + 1;
            }
        } else {
            lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games, bills, n, billIndex);
            gameIndex := n; // Fast-forward gameIndex as no more bills are available
        }
    }
    assert result == countBuyableGames(games, bills);
}
// </vc-code>

