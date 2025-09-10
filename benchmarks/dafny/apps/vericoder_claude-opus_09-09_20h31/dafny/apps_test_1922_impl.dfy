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
lemma CountFaceDownCardsNonNegative(N: int, M: int)
    requires ValidInput(N, M)
    ensures CountFaceDownCards(N, M) >= 0
{
    if N == 1 && M == 1 {
        assert CountFaceDownCards(N, M) == 1;
    } else if N == 1 {
        assert M >= 1;
        if M == 1 {
            assert false; // This case is covered by N == 1 && M == 1
        } else if M == 2 {
            assert CountFaceDownCards(N, M) == M - 2 == 0;
        } else {
            assert M >= 3;
            assert CountFaceDownCards(N, M) == M - 2 >= 1;
        }
    } else if M == 1 {
        assert N >= 2;
        if N == 2 {
            assert CountFaceDownCards(N, M) == N - 2 == 0;
        } else {
            assert N >= 3;
            assert CountFaceDownCards(N, M) == N - 2 >= 1;
        }
    } else {
        assert N >= 2 && M >= 2;
        if N == 2 || M == 2 {
            assert (N - 2) * (M - 2) == 0;
        } else {
            assert N >= 3 && M >= 3;
            assert (N - 2) >= 1 && (M - 2) >= 1;
            assert (N - 2) * (M - 2) >= 1;
        }
        assert CountFaceDownCards(N, M) == (N - 2) * (M - 2) >= 0;
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
    if N == 1 && M == 1 {
        result := 1;
    } else if N == 1 {
        result := M - 2;
    } else if M == 1 {
        result := N - 2;
    } else {
        result := (N - 2) * (M - 2);
    }
    
    CountFaceDownCardsNonNegative(N, M);
}
// </vc-code>

