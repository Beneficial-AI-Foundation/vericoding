predicate ValidInput(a1: int, a2: int, k1: int, k2: int, n: int) {
    a1 >= 1 && a2 >= 1 && k1 >= 1 && k2 >= 1 && n >= 1
}

function MinimumSentOff(a1: int, a2: int, k1: int, k2: int, n: int): int
    requires ValidInput(a1, a2, k1, k2, n)
{
    var max_non_sendoff_cards := (k1 - 1) * a1 + (k2 - 1) * a2;
    if n - max_non_sendoff_cards > 0 then n - max_non_sendoff_cards else 0
}

function MaximumSentOff(a1: int, a2: int, k1: int, k2: int, n: int): int
    requires ValidInput(a1, a2, k1, k2, n)
{
    if k1 < k2 then
        var team1_sent := if n / k1 < a1 then n / k1 else a1;
        var remaining_cards := n - team1_sent * k1;
        team1_sent + remaining_cards / k2
    else
        var team2_sent := if n / k2 < a2 then n / k2 else a2;
        var remaining_cards := n - team2_sent * k2;
        team2_sent + remaining_cards / k1
}

predicate ValidResult(a1: int, a2: int, k1: int, k2: int, n: int, minimum: int, maximum: int)
    requires ValidInput(a1, a2, k1, k2, n)
{
    minimum >= 0 && maximum >= 0 &&
    minimum <= maximum &&
    maximum <= a1 + a2 &&
    minimum <= n &&
    maximum <= n &&
    minimum == MinimumSentOff(a1, a2, k1, k2, n) &&
    maximum == MaximumSentOff(a1, a2, k1, k2, n)
}

// <vc-helpers>
lemma MinimumSentOffCorrect(a1: int, a2: int, k1: int, k2: int, n: int)
    requires ValidInput(a1, a2, k1, k2, n)
    ensures MinimumSentOff(a1, a2, k1, k2, n) >= 0
    ensures MinimumSentOff(a1, a2, k1, k2, n) <= n
{
    var max_non_sendoff_cards := (k1 - 1) * a1 + (k2 - 1) * a2;
    if n - max_non_sendoff_cards > 0 {
        assert MinimumSentOff(a1, a2, k1, k2, n) == n - max_non_sendoff_cards;
    } else {
        assert MinimumSentOff(a1, a2, k1, k2, n) == 0;
    }
}

lemma MaximumSentOffBounds(a1: int, a2: int, k1: int, k2: int, n: int)
    requires ValidInput(a1, a2, k1, k2, n)
    ensures MaximumSentOff(a1, a2, k1, k2, n) >= 0
    ensures MaximumSentOff(a1, a2, k1, k2, n) <= a1 + a2
{
    if k1 < k2 {
        var team1_sent := if n / k1 < a1 then n / k1 else a1;
        var remaining_cards := n - team1_sent * k1;
        assert team1_sent >= 0 && team1_sent <= a1;
        assert remaining_cards >= 0;
        assert remaining_cards / k2 <= a2;
    } else {
        var team2_sent := if n / k2 < a2 then n / k2 else a2;
        var remaining_cards := n - team2_sent * k2;
        assert team2_sent >= 0 && team2_sent <= a2;
        assert remaining_cards >= 0;
        assert remaining_cards / k1 <= a1;
    }
}

lemma MaximumSentOffCorrect(a1: int, a2: int, k1: int, k2: int, n: int)
    requires ValidInput(a1, a2, k1, k2, n)
    ensures MaximumSentOff(a1, a2, k1, k2, n) >= 0
    ensures MaximumSentOff(a1, a2, k1, k2, n) <= a1 + a2
    ensures MaximumSentOff(a1, a2, k1, k2, n) <= n
{
    MaximumSentOffBounds(a1, a2, k1, k2, n);
    
    if k1 < k2 {
        var team1_sent := if n / k1 < a1 then n / k1 else a1;
        var remaining_cards := n - team1_sent * k1;
        assert team1_sent * k1 <= n;
        assert remaining_cards == n - team1_sent * k1 >= 0;
        assert team1_sent + remaining_cards / k2 <= team1_sent + remaining_cards;
        assert team1_sent + remaining_cards <= n;
    } else {
        var team2_sent := if n / k2 < a2 then n / k2 else a2;
        var remaining_cards := n - team2_sent * k2;
        assert team2_sent * k2 <= n;
        assert remaining_cards == n - team2_sent * k2 >= 0;
        assert team2_sent + remaining_cards / k1 <= team2_sent + remaining_cards;
        assert team2_sent + remaining_cards <= n;
    }
}

lemma MinMaxRelation(a1: int, a2: int, k1: int, k2: int, n: int)
    requires ValidInput(a1, a2, k1, k2, n)
    ensures MinimumSentOff(a1, a2, k1, k2, n) <= MaximumSentOff(a1, a2, k1, k2, n)
{
    MinimumSentOffCorrect(a1, a2, k1, k2, n);
    MaximumSentOffCorrect(a1, a2, k1, k2, n);
}
// </vc-helpers>

// <vc-spec>
method solve(a1: int, a2: int, k1: int, k2: int, n: int) returns (minimum: int, maximum: int)
    requires ValidInput(a1, a2, k1, k2, n)
    ensures ValidResult(a1, a2, k1, k2, n, minimum, maximum)
// </vc-spec>
// <vc-code>
{
    // Calculate minimum sent off
    var max_non_sendoff_cards := (k1 - 1) * a1 + (k2 - 1) * a2;
    if n - max_non_sendoff_cards > 0 {
        minimum := n - max_non_sendoff_cards;
    } else {
        minimum := 0;
    }
    
    // Calculate maximum sent off
    if k1 < k2 {
        var team1_sent := if n / k1 < a1 then n / k1 else a1;
        var remaining_cards := n - team1_sent * k1;
        maximum := team1_sent + remaining_cards / k2;
    } else {
        var team2_sent := if n / k2 < a2 then n / k2 else a2;
        var remaining_cards := n - team2_sent * k2;
        maximum := team2_sent + remaining_cards / k1;
    }
    
    MinimumSentOffCorrect(a1, a2, k1, k2, n);
    MaximumSentOffCorrect(a1, a2, k1, k2, n);
    MinMaxRelation(a1, a2, k1, k2, n);
}
// </vc-code>

