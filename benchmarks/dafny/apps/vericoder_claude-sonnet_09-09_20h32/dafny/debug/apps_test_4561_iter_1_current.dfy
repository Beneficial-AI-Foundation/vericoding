predicate ValidOutcome(outcome: string)
{
    outcome in {"delicious", "safe", "dangerous"}
}

function DaysPastBestBy(A: int, B: int): int
{
    B - A
}

function ExpectedOutcome(X: int, A: int, B: int): string
{
    var daysPast := DaysPastBestBy(A, B);
    if daysPast <= 0 then "delicious"
    else if daysPast <= X then "safe"  
    else "dangerous"
}

// <vc-helpers>
lemma ExpectedOutcomeIsValid(X: int, A: int, B: int)
    requires X >= 0
    ensures ValidOutcome(ExpectedOutcome(X, A, B))
{
    var daysPast := DaysPastBestBy(A, B);
    if daysPast <= 0 {
        assert ExpectedOutcome(X, A, B) == "delicious";
    } else if daysPast <= X {
        assert ExpectedOutcome(X, A, B) == "safe";
    } else {
        assert ExpectedOutcome(X, A, B) == "dangerous";
    }
}
// </vc-helpers>

// <vc-spec>
method DetermineFoodSafety(X: int, A: int, B: int) returns (outcome: string)
    requires X >= 0
    ensures outcome == ExpectedOutcome(X, A, B)
    ensures ValidOutcome(outcome)
// </vc-spec>
// <vc-code>
{
    var daysPast := DaysPastBestBy(A, B);
    if daysPast <= 0 {
        outcome := "delicious";
    } else if daysPast <= X {
        outcome := "safe";
    } else {
        outcome := "dangerous";
    }
    ExpectedOutcomeIsValid(X, A, B);
}
// </vc-code>

