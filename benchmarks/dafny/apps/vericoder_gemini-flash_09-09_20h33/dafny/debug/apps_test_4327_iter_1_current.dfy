predicate ValidInput(A: int, P: int)
{
    0 <= A <= 100 && 0 <= P <= 100
}

function TotalPieces(A: int, P: int): int
    requires ValidInput(A, P)
{
    A * 3 + P
}

function MaxPies(A: int, P: int): int
    requires ValidInput(A, P)
{
    TotalPieces(A, P) / 2
}

// <vc-helpers>
lemma total_pieces_non_negative(A: int, P: int)
  requires ValidInput(A, P)
  ensures TotalPieces(A, P) >= 0
{
  // A, P >= 0 from ValidInput, so A*3 >= 0 and P >= 0. Their sum is also >= 0.
}

lemma max_pies_non_negative(A: int, P: int)
  requires ValidInput(A, P)
  ensures MaxPies(A, P) >= 0
{
  total_pieces_non_negative(A, P);
  // TotalPieces(A, P) is non-negative, so TotalPieces(A, P) / 2 is also non-negative.
}

lemma max_pies_equality(A: int, P: int)
  requires ValidInput(A, P)
  ensures MaxPies(A, P) == (A * 3 + P) / 2
{
  // This is directly from the definitions of TotalPieces and MaxPies.
  // MaxPies(A, P) == TotalPieces(A, P) / 2 == (A * 3 + P) / 2
}
// </vc-helpers>

// <vc-spec>
method CalculateMaxPies(A: int, P: int) returns (pies: int)
    requires ValidInput(A, P)
    ensures pies == MaxPies(A, P)
    ensures pies >= 0
    ensures pies == (A * 3 + P) / 2
// </vc-spec>
// <vc-code>
{
  var totalPieces := A * 3 + P;
  pies := totalPieces / 2;

  // Proofs for postconditions
  // 1. ensures pies == MaxPies(A, P)
  //    This follows directly from the definition of MaxPies and the calculation.
  //    We know MaxPies(A, P) == TotalPieces(A, P) / 2
  //    And TotalPieces(A, P) == A * 3 + P
  //    So MaxPies(A, P) == (A * 3 + P) / 2
  //    And our code calculates pies as (A * 3 + P) / 2.
  max_pies_equality(A, P);

  // 2. ensures pies >= 0
  //    Requires proving TotalPieces(A, P) >= 0, then TotalPieces(A, P) / 2 >= 0.
  max_pies_non_negative(A, P);

  // 3. ensures pies == (A * 3 + P) / 2
  //    This is directly what the code calculates.
}
// </vc-code>

