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
    // Provide witnesses for the existential in CanReachTarget
    assert exists st, fin ::
        0 <= st < |s| &&
        s[st] in {'G', 'T'} &&
        (forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'}) &&
        (exists final0 ::
            st < final0 < |s| &&
            s[final0] in {'G', 'T'} &&
            (final0 - st) % k == 0 &&
            (forall pos :: st < pos < final0 && (pos - st) % k == 0 ==> s[pos] !in {'G', 'T', '#'}))
    by {
        // choose st = start, final0 = final
        assert 0 <= start < |s|;
        assert s[start] in {'G', 'T'};
        assert (forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'});
        assert exists final0 ::
            start < final0 < |s| &&
            s[final0] in {'G', 'T'} &&
            (final0 - start) % k == 0 &&
            (forall pos :: start < pos < final0 && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'})
        by {
            assert start < final < |s|;
            assert s[final] in {'G', 'T'};
            assert (final - start) % k == 0;
            assert forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'}
            by {
                reveal_forall;
            }
        }
    }
}

lemma BlockedImpliesNoReach(s: string, k: int, start: int, blockPos: int)
    requires k > 0
    requires 0 <= start < |s|
    requires s[start] in {'G', 'T'}
    requires forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'}
    requires start < blockPos < |s|
    requires (blockPos - start) % k == 0
    requires forall j :: start < j < blockPos && (j - start) % k == 0 ==> s[j] == '.'
    requires s[blockPos] == '#'
    ensures not CanReachTarget(s, k)
{
    if CanReachTarget(s, k) {
        var st0, final0 :| 0 <= st0 < |s| &&
                         s[st0] in {'G', 'T'} &&
                         (forall j :: 0 <= j < st0 ==> s[j] !in {'G', 'T'}) &&
                         st0 < final0 < |s| &&
                         s[final0] in {'G', 'T'} &&
                         (final0 - st0) % k == 0 &&
                         (forall pos :: st0 < pos < final0 && (pos - st0) % k == 0 ==> s[pos] !in {'G', 'T', '#'});
        if start < st0 {
            assert false;
        }
        if st0 < start {
            assert false;
        }
        assert st0 == start;
        if final0 == blockPos {
            assert false;
        }
        if final0 > blockPos {
            assert false;
        }
    }
}

lemma NoFinalBecauseBoundary(s: string, k: int, start: int, pos: int)
    requires k > 0
    requires 0 <= start < |s|
    requires s[start] in {'G', 'T'}
    requires forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'}
    requires start <= pos < |s|
    requires (pos - start) % k == 0
    requires forall j :: start < j < pos && (j - start) % k == 0 ==> s[j] == '.'
    requires pos + k >= |s|
    requires (pos == start) || s[pos] == '.'
    ensures not CanReachTarget(s, k)
{
    if CanReachTarget(s, k) {
        var st0, final0 :| 0 <= st0 < |s| &&
                         s[st0] in {'G', 'T'} &&
                         (forall j :: 0 <= j < st0 ==> s[j] !in {'G', 'T'}) &&
                         st0 < final0 < |s| &&
                         s[final0] in {'G', 'T'} &&
                         (final0 - st0) % k == 0 &&
                         (forall pos0 :: st0 < pos0 < final0 && (pos0 - st0) % k == 0 ==> s[pos0] !in {'G', 'T', '#'});
        if start < st0 {
            assert false;
        }
        if st0 < start {
            assert false;
        }
        assert st0 == start;
        // final0 must be <= pos because any multiple greater than pos would be >= pos+k >= |s|
        if final0 > pos {
            assert false;
        }
        // If final0 < pos then by the forall assumption that multiple is '.', contradiction.
        if final0 < pos {
            assert false;
        }
        // If final0 == pos then either pos == start (impossible since final0 > start) or s[pos] == '.'
        // But we required (pos == start) || s[pos] == '.', so both lead to contradiction.
        if final0 == pos {
            assert false;
        }
    }
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

