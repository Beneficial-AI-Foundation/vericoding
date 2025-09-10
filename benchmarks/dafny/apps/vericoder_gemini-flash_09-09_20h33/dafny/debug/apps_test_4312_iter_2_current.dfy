predicate ValidInput(A: int, B: int, C: int, D: int)
{
  1 <= A <= 100 && 1 <= B <= 100 && 1 <= C <= 100 && 1 <= D <= 100
}

function TurnsToDefeat(health: int, strength: int): int
  requires strength > 0
{
  (health + strength - 1) / strength
}

predicate TakahashiWins(A: int, B: int, C: int, D: int)
  requires ValidInput(A, B, C, D)
{
  var takahashi_turns := TurnsToDefeat(C, B);
  var aoki_turns := TurnsToDefeat(A, D);
  aoki_turns >= takahashi_turns
}

// <vc-helpers>
function CeilDiv(numerator: int, denominator: int): int
  requires denominator > 0
  ensures CeilDiv(numerator, denominator) == (numerator + denominator - 1) / denominator
{
  (numerator + denominator - 1) / denominator
}

lemma lemma_TurnsToDefeat_CeilDiv(health: int, strength: int)
  requires strength > 0
  ensures TurnsToDefeat(health, strength) == CeilDiv(health, strength)
{
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int, D: int) returns (result: string)
  requires ValidInput(A, B, C, D)
  ensures result == (if TakahashiWins(A, B, C, D) then "Yes" else "No")
  ensures result == "Yes" || result == "No"
// </vc-spec>
// <vc-code>
{
  var takahashi_turns_to_defeat := CeilDiv(C, B);
  var aoki_turns_to_defeat := CeilDiv(A, D);

  if aoki_turns_to_defeat >= takahashi_turns_to_defeat
  {
    result := "Yes";
  }
  else
  {
    result := "No";
  }
  
  // Prove postcondition
  lemma_TurnsToDefeat_CeilDiv(C, B);
  lemma_TurnsToDefeat_CeilDiv(A, D);

  assert takahashi_turns_to_defeat == TurnsToDefeat(C,B);
  assert aoki_turns_to_defeat == TurnsToDefeat(A,D); // Fix: ReturnsToDefeat to TurnsToDefeat
  
  if aoki_turns_to_defeat >= takahashi_turns_to_defeat {
    assert TakahashiWins(A, B, C, D);
    assert result == "Yes";
  } else {
    assert !TakahashiWins(A, B, C, D);
    assert result == "No";
  }
  
  assert result == (if TakahashiWins(A, B, C, D) then "Yes" else "No");
  assert result == "Yes" || result == "No";
}
// </vc-code>

