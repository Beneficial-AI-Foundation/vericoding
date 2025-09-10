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

// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int, D: int) returns (result: string)
  requires ValidInput(A, B, C, D)
  ensures result == (if TakahashiWins(A, B, C, D) then "Yes" else "No")
  ensures result == "Yes" || result == "No"
// </vc-spec>
// <vc-code>
{
  var takahashi_turns := TurnsToDefeat(C, B);
  var aoki_turns := TurnsToDefeat(A, D);
  
  if aoki_turns >= takahashi_turns {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

