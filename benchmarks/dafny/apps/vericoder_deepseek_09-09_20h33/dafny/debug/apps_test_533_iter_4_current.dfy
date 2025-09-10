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
lemma LemmaDivMod(x: int, d: int)
  requires d > 0
  ensures x == d * (x / d) + x % d
  ensures 0 <= x % d < d
{
}

lemma LemmaDivLeq(x: int, y: int, d: int)
  requires d > 0
  requires x <= y
  ensures x / d <= y / d
{
  LemmaDivMod(x, d);
  LemmaDivMod(y, d);
}

lemma LemmaDivMult(x: int, d: int)
  requires d > 0
  requires x >= 0
  ensures x / d <= x
{
  if x > 0 {
    LemmaDivMod(x, d);
    assert d * (x / d) <= x;
  }
}

lemma LemmaDivBound(x: int, d: int)
  requires d > 0
  ensures x - d * (x / d) >= 0
{
  LemmaDivMod(x, d);
}

lemma LemmaMinMaxConsistency(a1: int, a2: int, k1: int, k2: int, n: int)
  requires ValidInput(a1, a2, k1, k2, n)
  ensures MinimumSentOff(a1, a2, k1, k2, n) <= MaximumSentOff(a1, a2, k1, k2, n)
{
  var min := MinimumSentOff(a1, a2, k1, k2, n);
  var max := MaximumSentOff(a1, a2, k1, k2, n);
  
  // Minimum is non-negative and we can always assign at least the minimum
  assert min >= 0;
  
  if k1 < k2 {
    var team1_possible := if n / k1 < a1 then n / k1 else a1;
    var remaining_cards := n - team1_possible * k1;
    var team2_possible := remaining_cards / k2;
    if team2_possible > a2 {
      team2_possible := a2;
    }
    var calculated_max := team1_possible + team2_possible;
    
    // The maximum calculation must be at least the minimum
    var max_non_sendoff := (k1 - 1) * a1 + (k2 - 1) * a2;
    assert min == if n > max_non_sendoff then n - max_non_sendoff else 0;
    assert calculated_max >= min;
  } else {
    var team2_possible := if n / k2 < a2 then n / k2 else a2;
    var remaining_cards := n - team2_possible * k2;
    var team1_possible := remaining_cards / k1;
    if team1_possible > a1 {
      team1_possible := a1;
    }
    var calculated_max := team2_possible + team1_possible;
    
    var max_non_sendoff := (k1 - 1) * a1 + (k2 - 1) * a2;
    assert min == if n > max_non_sendoff then n - max_non_sendoff else 0;
    assert calculated_max >= min;
  }
}

lemma LemmaMaxBoundByTotalPlayers(a1: int, a2: int, k1: int, k2: int, n: int)
  requires ValidInput(a1, a2, k1, k2, n)
  ensures MaximumSentOff(a1, a2, k1, k2, n) <= a1 + a2
{
  if k1 < k2 {
    var team1_sent := if n / k1 < a1 then n / k1 else a1;
    var team2_sent_bound := if n - team1_sent * k1 <= 0 then 0 else (n - team1_sent * k1) / k2;
    if team2_sent_bound > a2 {
      team2_sent_bound := a2;
    }
    assert team1_sent + team2_sent_bound <= a1 + a2;
  } else {
    var team2_sent := if n / k2 < a2 then n / k2 else a2;
    var team1_sent_bound := if n - team2_sent * k2 <= 0 then 0 else (n - team2_sent * k2) / k1;
    if team1_sent_bound > a1 {
      team1_sent_bound := a1;
    }
    assert team2_sent + team1_sent_bound <= a1 + a2;
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
  var max_non_sendoff := (k1 - 1) * a1 + (k2 - 1) * a2;
  minimum := if n > max_non_sendoff then n - max_non_sendoff else 0;
  
  if k1 < k2 {
    var team1_possible := n / k1;
    var team1_sent := if team1_possible < a1 then team1_possible else a1;
    var remaining_cards := n - team1_sent * k1;
    var team2_possible := remaining_cards / k2;
    var team2_sent := if team2_possible < a2 then team2_possible else a2;
    maximum := team1_sent + team2_sent;
    
    // Verification hints
    assert team1_sent >= 0 && team2_sent >= 0;
    assert team1_sent <= a1 && team2_sent <= a2;
    assert team1_sent * k1 + team2_sent * k2 <= n;
  } else {
    var team2_possible := n / k2;
    var team2_sent := if team2_possible < a2 then team2_possible else a2;
    var remaining_cards := n - team2_sent * k2;
    var team1_possible := remaining_cards / k1;
    var team1_sent := if team1_possible < a1 then team1_possible else a1;
    maximum := team2_sent + team1_sent;
    
    // Verification hints
    assert team1_sent >= 0 && team2_sent >= 0;
    assert team1_sent <= a1 && team2_sent <= a2;
    assert team1_sent * k1 + team2_sent * k2 <= n;
  }
}
// </vc-code>

