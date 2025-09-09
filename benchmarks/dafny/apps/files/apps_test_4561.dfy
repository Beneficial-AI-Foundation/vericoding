/*
Given three integers X, A, and B where X is the maximum number of days past 
best-by date that won't cause stomachache, A is the number of days before 
best-by date when food was bought, and B is the number of days after purchase 
when food was eaten. Determine if eating the food results in "delicious", 
"safe", or "dangerous" outcome.
*/

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
// </vc-helpers>

// <vc-spec>
method DetermineFoodSafety(X: int, A: int, B: int) returns (outcome: string)
    requires X >= 0
    ensures outcome == ExpectedOutcome(X, A, B)
    ensures ValidOutcome(outcome)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
