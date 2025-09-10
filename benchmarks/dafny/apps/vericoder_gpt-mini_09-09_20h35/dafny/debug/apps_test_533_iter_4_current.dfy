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
lemma MinUnfold(a1: int, a2: int, k1: int, k2: int, n: int)
    requires ValidInput(a1, a2, k1, k2, n)
    ensures MinimumSentOff(a1, a2, k1, k2, n) ==
            (if n - ((k1 - 1) * a1 + (k2 - 1) * a2) > 0 then n - ((k1 - 1) * a1 + (k2 - 1) * a2) else 0)
{
    // Unfold the function by asserting its definition
    assert MinimumSentOff(a1, a2, k1, k2, n) ==
           (if n - ((k1 - 1) * a1 + (k2 - 1) * a2) > 0 then n - ((k1 - 1) * a1 + (k2 - 1) * a2) else 0);
}

lemma MaxUnfold(a1: int, a2: int, k1: int, k2: int, n: int)
    requires ValidInput(a1, a2, k1, k2, n)
    ensures MaximumSentOff(a1, a2, k1, k2, n) ==
            (if k1 < k2 then
                (if n / k1 < a1 then n / k1 else a1) +
                (n - (if n / k1 < a1 then n / k1 else a1) * k1) / k2
             else
                (if n / k2 < a2 then n / k2 else a2) +
                (n - (if n / k2 < a2 then n / k2 else a2) * k2) / k1)
{
    if k1 < k2 {
        var team1_sent := if n / k1 < a1 then n / k1 else a1;
        var remaining := n - team1_sent * k1;
        assert MaximumSentOff(a1, a2, k1, k2, n) ==
               team1_sent + remaining / k2;
    } else {
        var team2_sent := if n / k2 < a2 then n / k2 else a2;
        var remaining := n - team2_sent * k2;
        assert MaximumSentOff(a1, a2, k1, k2, n) ==
               team2_sent + remaining / k1;
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

  // Help the verifier by unfolding the definitions
  MinUnfold(a1, a2, k1, k2, n);
  MaxUnfold(a1, a2, k1, k2, n);

  // Explicitly assert the result equalities (these follow from the assignments)
  assert minimum == MinimumSentOff(a1, a2, k1, k2, n);
  assert maximum == MaximumSentOff(a1, a2, k1, k2, n);

  // Basic bounds that follow from the definitions
  assert minimum >= 0;
  assert maximum >= 0;
  assert minimum <= maximum;
  assert minimum <= n;
  assert maximum <= n;
  assert maximum <= a1 + a2;
}
// </vc-code>

