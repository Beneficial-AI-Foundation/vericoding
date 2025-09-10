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
function method CountBuyableGamesIteration(games: seq<int>, bills: seq<int>, gameIndex: int, billIndex: int): int
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

lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games: seq<int>, bills: seq<int>, gameIndex: int, billIndex: int)
    returns (result: int)
    requires 0 <= gameIndex <= |games|
    requires 0 <= billIndex <= |bills|
    requires forall i :: 0 <= i < |games| ==> games[i] >= 1
    requires forall i :: 0 <= i < |bills| ==> bills[i] >= 1
    ensures CountBuyableGamesIteration(games, bills, gameIndex, billIndex) == countBuyableGames(games[gameIndex..], bills[billIndex..])
    decreases (|games| - gameIndex) + (|bills| - billIndex)
{
    if gameIndex == |games| || billIndex == |bills| {
        // Base cases: if no more games or no more bills, both should return 0
        // countBuyableGames(empty, any) == 0
        // countBuyableGames(any, empty) == 0
    } else if bills[billIndex] >= games[gameIndex] {
        lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games, bills, gameIndex + 1, billIndex + 1);
    } else {
        lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games, bills, gameIndex + 1, billIndex);
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

    // Initial loop invariant setup
    // Before the loop, gameIndex = 0, billIndex = 0, result = 0.
    // We aim to show that at each step, 'result' accumulates the count of buyable games
    // up to the current 'gameIndex' and 'billIndex', based on a hypothetical interpretation
    // of an iterative process for countBuyableGames.
    // The key is to prove that the final 'result' equals the total count.
    while gameIndex < n
        invariant 0 <= gameIndex <= n
        invariant 0 <= billIndex <= m
        // This invariant implicitly links the loop state to the total count.
        // The difficulty with a simple iterative proof for countBuyableGames is that it's
        // inherently recursive on two sequences, where one might not advance.
        // The iterative approach needs careful modeling of the state.

        // Let's refine the invariant to make it more precise.
        // We know that `CountBuyableGamesIteration(games, bills, gameIndex, billIndex)`
        // calculates the remaining buyable games.
        // The total `countBuyableGames(games, bills)` is `result + CountBuyableGamesIteration(games, bills, gameIndex, billIndex)`.
        // This holds if 'result' truly represents the games bought up to `gameIndex`, and `billIndex` is correctly advanced.
        invariant countBuyableGames(games, bills) ==
                  result + CountBuyableGamesIteration(games, bills, gameIndex, billIndex)
        invariant forall i :: 0 <= i < |games| ==> games[i] >= 1
        invariant forall i :: 0 <= i < |bills| ==> bills[i] >= 1
        decreases n - gameIndex
    {
        if billIndex < m {
            if bills[billIndex] >= games[gameIndex] {
                result := result + 1;
                billIndex := billIndex + 1;
                gameIndex := gameIndex + 1;
            } else {
                gameIndex := gameIndex + 1;
            }
        } else {
            // No more bills, so no more games can be bought.
            // The remaining `CountBuyableGamesIteration` will return 0.
            // We can fast-forward `gameIndex` to `n`.
            gameIndex := n;
        }
        // At each step, re-establish the relationship for the invariant
        lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games, bills, gameIndex, billIndex);
    }
    // After the loop, gameIndex == n.
    // This means `CountBuyableGamesIteration(games, bills, n, billIndex)` will be 0.
    // So, `countBuyableGames(games, bills) == result + 0`, which means `result == countBuyableGames(games, bills)`.
}
// </vc-code>

