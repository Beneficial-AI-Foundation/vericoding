predicate ValidInput(n: int, m: seq<int>) {
    n > 0 && |m| == n && 
    forall i :: 0 <= i < n ==> 0 <= m[i] < i + 1
}

predicate ValidSolution(n: int, m: seq<int>, dm: seq<int>) {
    |dm| == n && |m| == n &&
    (forall i :: 0 <= i < n ==> dm[i] >= m[i] + 1) &&
    (forall i :: 0 <= i < n - 1 ==> dm[i] <= dm[i + 1])
}

function SumBelow(m: seq<int>, dm: seq<int>): int
    requires |m| == |dm|
{
    if |m| == 0 then 0
    else (dm[0] - 1 - m[0]) + SumBelow(m[1..], dm[1..])
}

// <vc-helpers>
function SumBelowIndex(m: seq<int>, dm: seq<int>, i: int): int
    requires |m| == |dm|
    requires 0 <= i <= |m|
{
    if i == |m| then 0
    else (dm[i] - 1 - m[i]) + SumBelowIndex(m, dm, i + 1)
}

lemma SumBelowLemma(m: seq<int>, dm: seq<int>)
    requires |m| == |dm|
    ensures SumBelow(m, dm) == SumBelowIndex(m, dm, 0)
    decreases |m|
{
    if |m| == 0 {
    } else {
        calc {
            SumBelow(m, dm);
            (dm[0] - 1 - m[0]) + SumBelow(m[1..], dm[1..]);
            { SumBelowLemma(m[1..], dm[1..]); }
            (dm[0] - 1 - m[0]) + SumBelowIndex(m[1..], dm[1..], 0);
            (dm[0] - 1 - m[0]) + SumBelowIndex(m, dm, 1);
            SumBelowIndex(m, dm, 0);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: seq<int>) returns (result: int)
    requires ValidInput(n, m)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var dm := new int[n];
    if n == 0 {
        return 0;
    }

    dm[0] := m[0] + 1; // Since m[0] >= 0, dm[0] >= 1

    var i := 1;
    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> dm[k] >= m[k] + 1
        invariant forall k :: 0 <= k < i - 1 ==> dm[k] <= dm[k + 1]
    {
        dm[i] := m[i] + 1;
        if dm[i] <= dm[i-1] {
            dm[i] := dm[i-1] + 1;
        }
        i := i + 1;
    }

    // Prove conditions for ValidSolution
    // 1. |dm| == n && |m| == n (implied by initialization and invariant)
    // 2. (forall i :: 0 <= i < n ==> dm[i] >= m[i] + 1)
    // This is maintained by dm[i] := max(m[i] + 1, dm[i-1] + 1) for i > 0, and dm[0] = m[0] + 1.
    // So dm[i] >= m[i] + 1 is always true.
    // 3. (forall i :: 0 <= i < n - 1 ==> dm[i] <= dm[i + 1])
    // This is maintained by dm[i] := max(m[i] + 1, dm[i-1] + 1). For i > 0, dm[i] is defined such that dm[i] >= dm[i-1] + 1.
    // So dm[k] <= dm[k+1] is always true for k > 0.
    // For k=0, dm[0] <= dm[1] holds because dm[1] is at least dm[0]+1.

    // Calculate result as SumBelow(m, dm)
    SumBelowLemma(m, dm);
    result := SumBelow(m, dm);
    return result;
}
// </vc-code>

