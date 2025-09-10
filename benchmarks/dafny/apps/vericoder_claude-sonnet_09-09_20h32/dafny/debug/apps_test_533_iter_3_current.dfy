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
lemma MinimumSentOffProperties(a1: int, a2: int, k1: int, k2: int, n: int)
    requires ValidInput(a1, a2, k1, k2, n)
    ensures MinimumSentOff(a1, a2, k1, k2, n) >= 0
    ensures MinimumSentOff(a1, a2, k1, k2, n) <= n
    ensures MinimumSentOff(a1, a2, k1, k2, n) <= a1 + a2
{
    var max_non_sendoff_cards := (k1 - 1) * a1 + (k2 - 1) * a2;
    if n - max_non_sendoff_cards > 0 {
        assert MinimumSentOff(a1, a2, k1, k2, n) == n - max_non_sendoff_cards;
        assert MinimumSentOff(a1, a2, k1, k2, n) <= n;
        assert max_non_sendoff_cards >= 0;
        assert n - max_non_sendoff_cards <= n;
        assert max_non_sendoff_cards == (k1 - 1) * a1 + (k2 - 1) * a2;
        assert (k1 - 1) * a1 >= 0 && (k2 - 1) * a2 >= 0;
    } else {
        assert MinimumSentOff(a1, a2, k1, k2, n) == 0;
    }
}

lemma MaximumSentOffProperties(a1: int, a2: int, k1: int, k2: int, n: int)
    requires ValidInput(a1, a2, k1, k2, n)
    ensures MaximumSentOff(a1, a2, k1, k2, n) >= 0
    ensures MaximumSentOff(a1, a2, k1, k2, n) <= n
    ensures MaximumSentOff(a1, a2, k1, k2, n) <= a1 + a2
    ensures MaximumSentOff(a1, a2, k1, k2, n) >= MinimumSentOff(a1, a2, k1, k2, n)
{
    if k1 < k2 {
        var team1_sent := if n / k1 < a1 then n / k1 else a1;
        var remaining_cards := n - team1_sent * k1;
        var team2_sent := remaining_cards / k2;
        assert team1_sent <= a1;
        assert team2_sent <= a2;
        assert team1_sent + team2_sent <= a1 + a2;
        assert team1_sent * k1 <= n;
        assert team2_sent * k2 <= remaining_cards;
        assert team1_sent + team2_sent <= n;
    } else {
        var team2_sent := if n / k2 < a2 then n / k2 else a2;
        var remaining_cards := n - team2_sent * k2;
        var team1_sent := remaining_cards / k1;
        assert team2_sent <= a2;
        assert team1_sent <= a1;
        assert team2_sent + team1_sent <= a1 + a2;
        assert team2_sent * k2 <= n;
        assert team1_sent * k1 <= remaining_cards;
        assert team2_sent + team1_sent <= n;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(a1: int, a2: int, k1: int, k2: int, n: int) returns (minimum: int, maximum: int)
    requires ValidInput(a1, a2, k1, k2, n)
    ensures ValidResult(a1, a2, k1, k2, n, minimum, maximum)
// </vc-spec>
// <vc-code>
{
    minimum := MinimumSentOff(a1, a2, k1, k2, n);
    maximum := MaximumSentOff(a1, a2, k1, k2, n);
    
    MinimumSentOffProperties(a1, a2, k1, k2, n);
    MaximumSentOffProperties(a1, a2, k1, k2, n);
}
// </vc-code>

