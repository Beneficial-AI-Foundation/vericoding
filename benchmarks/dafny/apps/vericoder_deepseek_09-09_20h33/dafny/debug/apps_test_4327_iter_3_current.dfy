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
lemma MaxPiesLemma(A: int, P: int)
  requires ValidInput(A, P)
  ensures MaxPies(A, P) == (A * 3 + P) / 2
{
  // This lemma connects the two equivalent definitions
}

lemma NonNegativeLemma(A: int, P: int)
  requires ValidInput(A, P)
  ensures MaxPies(A, P) >= 0
{
  // Since A and P are non-negative, TotalPieces will be non-negative
  // and division by 2 of non-negative number gives non-negative result
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
  assert MaxPies(A, P) == (A * 3 + P) / 2 by {
    MaxPiesLemma(A, P);
  }
  pies := (A * 3 + P) / 2;
}
// </vc-code>

