predicate ValidInput(A: int, B: int, C: int)
{
    1 <= A <= 10 && 1 <= B <= 10 && 1 <= C <= 10
}

predicate CanFormHaiku(A: int, B: int, C: int)
{
    (A == 5 && B == 5 && C == 7) ||
    (A == 5 && B == 7 && C == 5) ||
    (A == 7 && B == 5 && C == 5)
}

predicate ValidOutput(result: string)
{
    result in {"YES", "NO"}
}

// <vc-helpers>
lemma lemma_CanFormHaiku_permutations(A: int, B: int, C: int)
  requires ValidInput(A,B,C)
  ensures (A == 5 && B == 5 && C == 7) || (A == 5 && B == 7 && C == 5) || (A == 7 && B == 5 && C == 5) <==>
          (CanFormHaiku(A,B,C))
{
  // The predicate CanFormHaiku is already defined to cover these permutations
  // This lemma is mostly for documentation or if additional permutations were to be considered
  // and we needed to prove their equivalence to the defined predicate.
  // In this simple case, the equivalence is direct from the definition.
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int) returns (result: string)
    requires ValidInput(A, B, C)
    ensures ValidOutput(result)
    ensures result == "YES" <==> CanFormHaiku(A, B, C)
// </vc-spec>
// <vc-code>
{
  if CanFormHaiku(A, B, C)
  {
    result := "YES";
  }
  else
  {
    result := "NO";
  }
  
  // Prove ensures clause: result == "YES" <==> CanFormHaiku(A, B, C)
  // Case 1: If CanFormHaiku(A, B, C) is true
  // Then result is set to "YES". So "YES" == "YES" is true, and CanFormHaiku(A,B,C) is true.
  // Therefore, true <==> true, which is true.
  
  // Case 2: If CanFormHaiku(A, B, C) is false
  // Then result is set to "NO". So "NO" == "YES" is false, and CanFormHaiku(A,B,C) is false.
  // Therefore, false <==> false, which is true.

  // Prove ensures clause: ValidOutput(result)
  // If result is "YES", then "YES" is in {"YES", "NO"}.
  // If result is "NO", then "NO" is in {"YES", "NO"}.
  // In both cases, ValidOutput(result) holds.
}
// </vc-code>

