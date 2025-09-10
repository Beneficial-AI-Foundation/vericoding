predicate ValidInput(n: int, k: int, s: string)
{
    n >= 2 &&
    1 <= k < n &&
    |s| == n &&
    (exists i :: 0 <= i < |s| && s[i] == 'G') &&
    (exists i :: 0 <= i < |s| && s[i] == 'T') &&
    (forall i :: 0 <= i < |s| ==> s[i] in {'G', 'T', '.', '#'}) &&
    (forall i, j :: 0 <= i < j < |s| && s[i] == 'G' ==> s[j] != 'G') &&
    (forall i, j :: 0 <= i < j < |s| && s[i] == 'T' ==> s[j] != 'T')
}

function FindFirstGOrT(s: string): int
    requires exists i :: 0 <= i < |s| && s[i] in {'G', 'T'}
{
    if s[0] in {'G', 'T'} then 0
    else FindFirstGOrT(s[1..]) + 1
}

predicate CanReachTarget(s: string, k: int)
    requires k > 0
{
    exists start :: 
        0 <= start < |s| && 
        s[start] in {'G', 'T'} &&
        (forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'}) &&
        (exists final :: 
            start < final < |s| &&
            s[final] in {'G', 'T'} &&
            (final - start) % k == 0 &&
            (forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'})
        )
}

// <vc-helpers>
lemma ReachFoundImpliesCanReach(s: string, k: int, start: int, final: int)
    requires k > 0
    requires 0 <= start < |s|
    requires s[start] in {'G', 'T'}
    requires forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'}
    requires start < final < |s|
    requires (final - start) % k == 0
    requires forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] == '.'
{
    // Provide explicit witnesses for the existential in CanReachTarget
    assert exists st, fin ::
        st == start &&
        fin == final &&
        0 <= st < |s| &&
        s[st] in {'G', 'T'} &&
        (forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'}) &&
        st < fin < |s| &&
        s[fin] in {'G', 'T'} &&
        (fin - st) % k == 0 &&
        (forall pos :: st < pos < fin && (pos - st) % k == 0 ==> s[pos] !in {'G', 'T', '#'});
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, s: string) returns (result: string)
    requires ValidInput(n, k, s)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanReachTarget(s, k)
// </vc-spec>
// <vc-code>
{
    var start := FindFirstGOrT(s);
    var pos := start + k;
    // If there's no multiple beyond start, immediately conclude NO
    if pos >= |s| {
        NoFinalBecauseBoundary(s, k, start, start);
        return "NO";
    }
    // Explore multiples of k starting from start+k
    while pos < |s|
        invariant 0 <= start < |s|
        invariant s[start] in {'G', 'T'}
        invariant forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'}
        invariant forall j :: start < j < pos && (j - start) % k == 0 ==> s[j] == '.'
        invariant (pos - start) % k == 0
        decreases |s| - pos
    {
        if s[pos] in {'G', 'T'} {
            ReachFoundImpliesCanReach(s, k, start, pos);
            return "YES";
        } else if s[pos] == '#' {
            BlockedImpliesNoReach(s, k, start, pos);
            return "NO";
        } else {
            pos := pos + k;
        }
    }
    var last := pos - k;
    NoFinalBecauseBoundary(s, k, start, last);
    return "NO";
}
// </vc-code>

