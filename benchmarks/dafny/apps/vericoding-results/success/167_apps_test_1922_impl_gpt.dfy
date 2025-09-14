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
lemma MulNonNeg(x: int, y: nat)
  requires x >= 0
  ensures x * y >= 0
  decreases y
{
  if y == 0 {
    assert x * y == 0;
  } else {
    MulNonNeg(x, y - 1);
    assert y >= 1;
    assert x * y == x * ((y - 1) + 1);
    assert x * ((y - 1) + 1) == x * (y - 1) + x;
    // from the recursive call, x*(y-1) >= 0 and x >= 0, hence the sum is >= 0
  }
}

lemma CountFaceDownCardsNonNeg(N: int, M: int)
  requires ValidInput(N, M)
  ensures CountFaceDownCards(N, M) >= 0
{
  if N == 1 && M == 1 {
    assert CountFaceDownCards(N, M) == 1;
  } else if N == 1 {
    assert M >= 2;
    assert CountFaceDownCards(N, M) == M - 2;
  } else if M == 1 {
    assert N >= 2;
    assert CountFaceDownCards(N, M) == N - 2;
  } else {
    assert N >= 2;
    assert M >= 2;
    var a: nat := N - 2;
    var b: nat := M - 2;
    assert CountFaceDownCards(N, M) == (N - 2) * (M - 2);
    assert (N - 2) == a && (M - 2) == b;
    MulNonNeg(a, b);
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
  result := CountFaceDownCards(N, M);
  CountFaceDownCardsNonNeg(N, M);
  assert result >= 0;
}
// </vc-code>

