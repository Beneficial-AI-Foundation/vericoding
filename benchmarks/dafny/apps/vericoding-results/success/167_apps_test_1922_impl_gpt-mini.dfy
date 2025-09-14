predicate ValidInput(N: int, M: int)
{
    N >= 1 && M >= 1
}

function CountFaceDownCards(N: int, M: int): int
    requires ValidInput(N, M)
{
    if N == 1 && M == 1 then 1
    else if N == 1 then M - 2
    else if M == 1 then N - 2
    else (N - 2) * (M - 2)
}

// <vc-helpers>
lemma NonZeroImpliesAtLeastTwo(x: int)
  requires x >= 1 && x != 1
  ensures x >= 2
{
  // If x < 2 then x <= 1. Combined with x >= 1 gives x == 1, contradicting x != 1.
  if x < 2 {
    assert x <= 1;
    assert x >= 1;
    assert x == 1;
    assert false;
  } else {
    // otherwise x >= 2
    assert x >= 2;
  }
}

lemma CountFaceDown_nonneg(N: int, M: int)
  requires ValidInput(N, M)
  ensures CountFaceDownCards(N, M) >= 0
{
  if N == 1 {
    if M == 1 {
      assert CountFaceDownCards(N, M) == 1;
      assert 1 >= 0;
    } else {
      NonZeroImpliesAtLeastTwo(M);
      assert M >= 2;
      assert CountFaceDownCards(N, M) == M - 2;
      assert M - 2 >= 0;
    }
  } else if M == 1 {
    NonZeroImpliesAtLeastTwo(N);
    assert N >= 2;
    assert CountFaceDownCards(N, M) == N - 2;
    assert N - 2 >= 0;
  } else {
    NonZeroImpliesAtLeastTwo(N);
    NonZeroImpliesAtLeastTwo(M);
    assert N >= 2 && M >= 2;
    assert CountFaceDownCards(N, M) == (N - 2) * (M - 2);
    assert N - 2 >= 0 && M - 2 >= 0;
    assert (N - 2) * (M - 2) >= 0;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, M: int) returns (result: int)
    requires ValidInput(N, M)
    ensures result == CountFaceDownCards(N, M)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  if N == 1 {
    if M == 1 {
      result := 1;
    } else {
      result := M - 2;
    }
  } else if M == 1 {
    result := N - 2;
  } else {
    result := (N - 2) * (M - 2);
  }

  assert result == CountFaceDownCards(N, M);
  CountFaceDown_nonneg(N, M);
  assert result >= 0;
}
// </vc-code>

