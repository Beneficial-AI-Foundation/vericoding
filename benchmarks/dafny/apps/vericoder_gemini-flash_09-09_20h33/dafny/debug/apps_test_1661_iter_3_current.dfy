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
    if gameIndex == |games| || billIndex == |bills| {
        // Base cases: if no more games or no more bills, both should return 0
        // countBuyableGames(empty, any) == 0  -- this is implied by the `if |games| == 0` clause in countBuyableGames
        // countBuyableGames(any, empty) == 0  -- this is implied by the `else if |bills| == 0` clause in countBuyableGames
        result := CountBuyableGamesIteration(games, bills, gameIndex, billIndex); // This line is not strictly needed but makes explicit the intention.
    } else if bills[billIndex] >= games[gameIndex] {
        var _ := lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games, bills, gameIndex + 1, billIndex + 1);
        result := CountBuyableGamesIteration(games, bills, gameIndex, billIndex);
    } else {
        var _ := lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games, bills, gameIndex + 1, billIndex);
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

    var _ := lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games, bills, 0, 0);

    while gameIndex < n
        invariant 0 <= gameIndex <= n
        invariant 0 <= billIndex <= m
        invariant countBuyableGames(games, bills) ==
                  result + CountBuyableGamesIteration(games, bills, gameIndex, billIndex)
        invariant forall i :: 0 <= i < |games| ==> games[i] >= 1
        invariant forall i :: 0 <= i < |bills| ==> bills[i] >= 1
        decreases n - gameIndex
    {
        if billIndex < m {
            if bills[billIndex] >= games[gameIndex] {
                // Prove the invariant holds after the update
                // Old Invariant: countBuyableGames(games,bills) == result_old + CountBuyableGamesIteration(games,bills,gameIndex_old,billIndex_old)
                // New result: result_old + 1
                // New indices: gameIndex_old+1, billIndex_old+1
                // We need to show: countBuyableGames(games,bills) == (result_old+1) + CountBuyableGamesIteration(games,bills,gameIndex_old+1,billIndex_old+1)
                // From definition of CountBuyableGamesIteration:
                // CountBuyableGamesIteration(games,bills,gameIndex_old,billIndex_old) == 1 + CountBuyableGamesIteration(games,bills,gameIndex_old+1,billIndex_old+1)
                // Substituting this into the old invariant:
                // countBuyableGames(games,bills) == result_old + (1 + CountBuyableGamesIteration(games,bills,gameIndex_old+1,billIndex_old+1))
                // This rearranges to:
                // countBuyableGames(games,bills) == (result_old+1) + CountBuyableGamesIteration(games,bills,gameIndex_old+1,billIndex_old+1)
                // This is exactly what we need to prove for the new state.
                var _ := lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games, bills, gameIndex + 1, billIndex + 1);
                result := result + 1;
                billIndex := billIndex + 1;
                gameIndex := gameIndex + 1;
            } else {
                // Prove the invariant holds after the update
                // Old Invariant: countBuyableGames(games,bills) == result_old + CountBuyableGamesIteration(games,bills,gameIndex_old,billIndex_old)
                // New result: result_old (unchanged)
                // New indices: gameIndex_old+1, billIndex_old (unchanged)
                // We need to show: countBuyableGames(games,bills) == result_old + CountBuyableGamesIteration(games,bills,gameIndex_old+1,billIndex_old)
                // From definition of CountBuyableGamesIteration:
                // CountBuyableGamesIteration(games,bills,gameIndex_old,billIndex_old) == CountBuyableGamesIteration(games,bills,gameIndex_old+1,billIndex_old)
                // Substituting this into the old invariant directly proves the new invariant.
                var _ := lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games, bills, gameIndex + 1, billIndex);
                gameIndex := gameIndex + 1;
            }
        } else {
            // billIndex >= m means no more bills are available.
            // Any further games cannot be bought.
            // In this case, CountBuyableGamesIteration(games, bills, gameIndex, billIndex) will evaluate to 0 because billIndex == |bills|.
            // So, countBuyableGames(games, bills) == result + 0.
            // We can advance gameIndex to n, and the invariant will still hold as CountBuyableGamesIteration will evaluate to 0 for any higher gameIndex up to n.
            var _ := lemma_CountBuyableGamesIteration_eq_countBuyableGames_slice(games, bills, n, billIndex);
            gameIndex := n;
        }
    }
}
// </vc-code>

