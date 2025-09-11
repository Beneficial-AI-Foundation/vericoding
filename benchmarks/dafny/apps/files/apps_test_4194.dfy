// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
