predicate ValidInput(n: int, m: int, A: seq<int>, queries: seq<int>)
{
    |A| == n && |queries| == m && n >= 1 && m >= 1 &&
    forall i :: 0 <= i < m ==> 1 <= queries[i] <= n
}

function DistinctCount(A: seq<int>, start: int): int
    requires 0 <= start < |A|
{
    |set j | start <= j < |A| :: A[j]|
}

// <vc-helpers>
lemma DistinctCountLemma(A: seq<int>, start: int, end: int)
    requires 0 <= start <= end <= |A|
    ensures DistinctCount(A, start) == DistinctCount(A, end) + CountDistinctInRange(A, start, end)
    decreases end - start
{
    if start == end {
        assert CountDistinctInRange(A, start, end) == 0;
    } else {
        DistinctCountLemma(A, start, end - 1);
        var s1 := set j | start <= j < end - 1 :: A[j];
        var s2 := set j | start <= j < end :: A[j];
        if A[end - 1] in s1 {
            assert s2 == s1;
        } else {
            assert s2 == s1 + {A[end - 1]};
        }
        assert CountDistinctInRange(A, start, end) == if A[end - 1] in s1 then |s1| else |s1| + 1;
    }
}

function CountDistinctInRange(A: seq<int>, start: int, end: int): int
    requires 0 <= start <= end <= |A|
{
    |set j | start <= j < end :: A[j]|
}

lemma DistinctCountDecomposition(A: seq<int>, start: int, mid: int, end: int)
    requires 0 <= start <= mid <= end <= |A|
    ensures DistinctCount(A, start) == DistinctCount(A, mid) + CountDistinctInRange(A, start, mid)
{
    DistinctCountLemma(A, start, mid);
}

lemma DistinctCountEquivalence(A: seq<int>, start: int)
    requires 0 <= start < |A|
    ensures DistinctCount(A, start) == CountDistinctInRange(A, start, |A|)
{
    DistinctCountLemma(A, start, |A|);
}

lemma SetLemma(A: seq<int>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= |A|
    ensures set m | i <= m < k :: A[m] == (set m | i <= m < j :: A[m]) + (set m | j <= m < k :: A[m])
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, A: seq<int>, queries: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, m, A, queries)
    ensures |result| == m
    ensures forall i :: 0 <= i < m ==> 
        result[i] == DistinctCount(A, queries[i] - 1)
// </vc-spec>
// <vc-code>
{
    result := [];
    var distinctFromEnd := new int[n];
    var seen: set<int> := {};
    
    for i := n - 1 downto 0
        invariant i >= -1 && i < n
        invariant distinctFromEnd.Length == n
        invariant forall j :: i < j < n ==> distinctFromEnd[j] == CountDistinctInRange(A, j, n)
        invariant seen == set k | i < k < n :: A[k]
    {
        seen := seen + {A[i]};
        distinctFromEnd[i] := |seen|;
        if i > 0 {
            SetLemma(A, i - 1, i, n);
        }
    }
    
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == distinctFromEnd[queries[j] - 1]
    {
        var idx := queries[i] - 1;
        DistinctCountEquivalence(A, idx);
        result := result + [distinctFromEnd[idx]];
        i := i + 1;
    }
}
// </vc-code>

