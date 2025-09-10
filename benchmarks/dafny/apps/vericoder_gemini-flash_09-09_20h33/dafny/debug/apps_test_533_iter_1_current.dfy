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

// </vc-helpers>

// <vc-spec>
method solve(a1: int, a2: int, k1: int, k2: int, n: int) returns (minimum: int, maximum: int)
    requires ValidInput(a1, a2, k1, k2, n)
    ensures ValidResult(a1, a2, k1, k2, n, minimum, maximum)
// </vc-spec>
// <vc-code>
{
    var min_sent_off: int;
    var max_sent_off: int;

    // Calculate minimum sent-off cards
    var max_non_sendoff_cards := (k1 - 1) * a1 + (k2 - 1) * a2;
    if n - max_non_sendoff_cards > 0 then
        min_sent_off := n - max_non_sendoff_cards;
    else
        min_sent_off := 0;

    // Calculate maximum sent-off cards
    if k1 < k2 then
        var team1_sent_a1: int;
        if n / k1 < a1 then
            team1_sent_a1 := n / k1;
        else
            team1_sent_a1 := a1;
        var remaining_cards_after_t1 := n - team1_sent_a1 * k1;
        max_sent_off := team1_sent_a1 + remaining_cards_after_t1 / k2;
    else
        var team2_sent_a2: int;
        if n / k2 < a2 then
            team2_sent_a2 := n / k2;
        else
            team2_sent_a2 := a2;
        var remaining_cards_after_t2 := n - team2_sent_a2 * k2;
        max_sent_off := team2_sent_a2 + remaining_cards_after_t2 / k1;
    
    return min_sent_off, max_sent_off;
}
// </vc-code>

