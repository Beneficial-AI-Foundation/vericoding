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
lemma SumNonNegative(s: seq<int>)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures sum(s) >= 0
{
    if |s| == 0 {
    } else {
        SumNonNegative(s[1..]);
    }
}

lemma SumBounds(s: seq<int>, N: int)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    requires sum(s) <= N
    ensures N - sum(s) >= 0
{
    SumNonNegative(s);
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
    } else {
        var totalDays := TotalAssignmentDays(A);
        if totalDays <= N {
            result := N - totalDays;
        } else {
            result := -1;
        }
    }
}
// </vc-code>

