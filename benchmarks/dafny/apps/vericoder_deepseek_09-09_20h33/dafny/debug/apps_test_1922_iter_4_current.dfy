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
lemma CountFaceDownCardsLemma(N: int, M: int)
  requires ValidInput(N, M)
  ensures CountFaceDownCards(N, M) >= 0
{
  if N == 1 && M == 1 {
  } else if N == 1 {
    assert M >= 1;
    assert M - 2 >= -1; // M could be 1, making it -1
  } else if M == 1 {
    assert N >= 1;
    assert N - 2 >= -1; // N could be 1, making it -1
  } else {
    assert N >= 2;
    assert M >= 2;
    assert N - 2 >= 0;
    assert M - 2 >= 0;
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
        assert N >= 2 && M >= 2;
        result := (N - 2) * (M - 2);
    }
}
// </vc-code>

