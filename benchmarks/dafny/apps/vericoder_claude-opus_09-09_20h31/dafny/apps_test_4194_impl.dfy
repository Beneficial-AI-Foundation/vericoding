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
lemma SumProperties(s: seq<int>)
    ensures sum(s) >= 0 || exists i :: 0 <= i < |s| && s[i] < 0
{
    if |s| == 0 {
        assert sum(s) == 0;
    } else {
        SumProperties(s[1..]);
    }
}

lemma SumNonNegative(s: seq<int>)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures sum(s) >= 0
{
    if |s| == 0 {
        assert sum(s) == 0;
    } else {
        SumNonNegative(s[1..]);
        assert sum(s) == s[0] + sum(s[1..]);
        assert s[0] >= 0;
        assert sum(s[1..]) >= 0;
    }
}

lemma SumAppend(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures sum(s[..i]) + s[i] == sum(s[..i+1])
{
    if i == 0 {
        assert s[..0] == [];
        assert sum([]) == 0;
        assert s[..1] == [s[0]];
        assert sum([s[0]]) == s[0];
    } else {
        assert s[..i+1][0] == s[0];
        assert s[..i+1][1..] == s[1..i+1];
        assert sum(s[..i+1]) == s[0] + sum(s[1..i+1]);
        
        assert s[..i][0] == s[0];
        assert s[..i][1..] == s[1..i];
        assert sum(s[..i]) == s[0] + sum(s[1..i]);
        
        assert s[1..][i-1] == s[i];
        SumAppend(s[1..], i-1);
        assert sum(s[1..][..i-1]) + s[1..][i-1] == sum(s[1..][..i]);
        assert s[1..][..i-1] == s[1..i];
        assert s[1..][..i] == s[1..i+1];
        assert sum(s[1..i]) + s[i] == sum(s[1..i+1]);
    }
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
        var totalDays := 0;
        var i := 0;
        
        while i < |A|
            invariant 0 <= i <= |A|
            invariant totalDays == sum(A[..i])
        {
            SumAppend(A, i);
            totalDays := totalDays + A[i];
            i := i + 1;
        }
        
        assert i == |A|;
        assert A[..i] == A;
        assert totalDays == sum(A);
        
        if totalDays <= N {
            result := N - totalDays;
        } else {
            result := -1;
        }
    }
}
// </vc-code>

