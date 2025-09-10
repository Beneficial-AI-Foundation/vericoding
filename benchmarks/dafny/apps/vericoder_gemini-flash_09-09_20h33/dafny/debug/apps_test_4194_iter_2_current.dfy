predicate ValidInput(N: int, M: int, A: seq<int>)
{
    N >= 0 && M >= 0 && M == |A|
}

predicate CanCompleteAllAssignments(N: int, A: seq<int>)
{
    sum(A) <= N
}

function TotalAssignmentDays(A: seq<int>): int
{
    sum(A)
}

function sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

// <vc-helpers>
lemma SummationProperty(A: seq<int>)
    ensures sum(A) == (if |A| == 0 then 0 else A[0] + sum(A[1..]))
{
    // This lemma is just stating the definition of sum,
    // which Dafny's SMT solver usually handles implicitly.
    // Explicitly proving it here doesn't add much, but it's good practice
    // to clarify. For this specific problem, it's not strictly necessary
    // as the SMT solver handles it, but included for completeness if needed elsewhere.
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, M: int, A: seq<int>) returns (result: int)
    requires ValidInput(N, M, A)
    ensures M == 0 ==> result == N
    ensures M > 0 && CanCompleteAllAssignments(N, A) ==> result == N - TotalAssignmentDays(A)
    ensures M > 0 && !CanCompleteAllAssignments(N, A) ==> result == -1
    ensures result >= -1
// </vc-spec>
// <vc-code>
{
    if M == 0 {
        result := N;
    } else if CanCompleteAllAssignments(N, A) {
        result := N - TotalAssignmentDays(A);
    } else {
        result := -1;
    }
}
// </vc-code>

