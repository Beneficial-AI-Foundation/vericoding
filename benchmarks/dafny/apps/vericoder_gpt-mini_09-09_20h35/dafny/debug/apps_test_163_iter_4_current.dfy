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
    assert exists st, fin ::
        0 <= st < |s| &&
        s[st] in {'G', 'T'} &&
        (forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'}) &&
        st < fin < |s| &&
        s[fin] in {'G', 'T'} &&
        (fin - st) % k == 0 &&
        (forall pos :: st < pos < fin && (pos - st) % k == 0 ==> s[pos] !in {'G', 'T', '#'})
    by {
        st := start;
        fin := final;
        assert 0 <= st < |s|;
        assert s[st] in {'G', 'T'};
        assert (forall j :: 0 <= j < st ==> s[j] !in {'G', 'T'});
        assert st < fin < |s|;
        assert s[fin] in {'G', 'T'};
        assert (fin - st) % k == 0;
        // From the precondition s[pos] == '.' for all relevant multiples,
        // we get s[pos] !in {'G','T','#'} for those positions.
        assert forall pos :: st < pos < fin && (pos - st) % k == 0 ==> s[pos] !in {'G', 'T', '#'};
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
    ensures !CanReachTarget(s, k)
{
    if CanReachTarget(s, k) {
        var st0, final0 :| 0 <= st0 < |s| &&
                         s[st0] in {'G', 'T'} &&
                         (forall j :: 0 <= j < st0 ==> s[j] !in {'G', 'T'}) &&
                         st0 < final0 < |s| &&
                         s[final0] in {'G', 'T'} &&
                         (final0 - st0) % k == 0 &&
                         (forall pos :: st0 < pos < final0 && (pos - st0) % k == 0 ==> s[pos] !in {'G', 'T', '#'});
        // st0 must equal start because start has no G/T before it.
        if st0 < start {
            // s[st0] in {'G','T'} and 0 <= st0 < start contradicts the assumption about start
            assert s[st0] in {'G', 'T'};
            assert 0 <= st0 < start;
            assert false;
        }
        if st0 > start {
            // s[start] in {'G','T'} and 0 <= start < st0 contradicts the forall for st0
            assert s[start] in {'G', 'T'};
            assert 0 <= start < st0;
            assert false;
        }
        assert st0 == start;
        // Now consider final0 relative to blockPos.
        if final0 == blockPos {
            // final0 is a G/T but blockPos is '#'
            assert s[final0] in {'G', 'T'};
            assert s[blockPos] == '#';
            assert false;
        }
        if final0 > blockPos {
            // blockPos is a multiple of k between start and final0, so from the witness property it must not be '#'
            assert (blockPos - st0) % k == 0;
            assert start < blockPos < final0;
            // from witness we have s[blockPos] !in {'G','T','#'}
            assert (forall pos :: st0 < pos < final0 && (pos - st0) % k == 0 ==> s[pos] !in {'G','T','#'});
            // instantiate the forall for pos = blockPos
            assert s[blockPos] !in {'G','T','#'};
            // but precondition says s[blockPos] == '#'
            assert s[blockPos] == '#';
            assert false;
        }
        // If final0 < blockPos then final0 is a multiple of k between start and blockPos, but those are '.' by precondition
        if final0 < blockPos {
            assert (final0 - start) % k == 0;
            assert start < final0 < blockPos;
            assert forall j :: start < j < blockPos && (j - start) % k == 0 ==> s[j] == '.';
            // hence s[final0] == '.', contradicting s[final0] in {'G','T'}
            assert s[final0] == '.';
            assert s[final0] in {'G', 'T'};
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
    ensures !CanReachTarget(s, k)
{
    if CanReachTarget(s, k) {
        var st0, final0 :| 0 <= st0 < |s| &&
                         s[st0] in {'G', 'T'} &&
                         (forall j :: 0 <= j < st0 ==> s[j] !in {'G', 'T'}) &&
                         st0 < final0 < |s| &&
                         s[final0] in {'G', 'T'} &&
                         (final0 - st0) % k == 0 &&
                         (forall pos0 :: st0 < pos0 < final0 && (pos0 - st0) % k == 0 ==> s[pos0] !in {'G', 'T', '#'});
        // st0 must be start
        if st0 < start {
            assert s[st0] in {'G','T'};
            assert 0 <= st0 < start;
            assert false;
        }
        if st0 > start {
            assert s[start] in {'G','T'};
            assert 0 <= start < st0;
            assert false;
        }
        assert st0 == start;
        // final0 is a multiple of k from start; but since pos + k >= |s|, any multiple > pos would be >= |s|
        // So final0 cannot be > pos.
        if final0 > pos {
            assert final0 >= pos + k;
            assert pos + k >= |s|;
            assert final0 >= |s|;
            assert false;
        }
        // If final0 < pos then by assumption that multiple is '.', contradiction with s[final0] in {'G','T'}
        if final0 < pos {
            assert start < final0 < pos;
            assert (final0 - start) % k == 0;
            assert forall j :: start < j < pos && (j - start) % k == 0 ==> s[j] == '.';
            assert s[final0] == '.';
            assert s[final0] in {'G','T'};
            assert false;
        }
        // If final0 == pos then either pos == start (impossible since final0 > start) or s[pos] == '.'
        if final0 == pos {
            // final0 > start by predicate, so pos != start; hence s[pos] == '.'
            assert s[pos] == '.';
            assert s[final0] in {'G','T'};
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

