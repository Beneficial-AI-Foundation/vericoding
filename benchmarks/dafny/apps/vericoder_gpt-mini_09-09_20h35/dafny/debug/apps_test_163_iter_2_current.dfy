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
        assert start == start; assert final == final;
        assert 0 <= start < |s|;
        assert s[start] in {'G', 'T'};
        assert (forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'});
        // inner existential
        assert exists final0 ::
            start < final0 < |s| &&
            s[final0] in {'G', 'T'} &&
            (final0 - start) % k == 0 &&
            (forall pos :: start < pos < final0 && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'})
        by {
            // final0 = final
            assert start < final < |s|;
            assert s[final] in {'G', 'T'};
            assert (final - start) % k == 0;
            // positions between are '.' hence not in {'G','T','#'}
            assert forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'}
            by {
                reveal_forall;
                // from s[pos]=='.' we get s[pos] !in {'G','T','#'}
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
        // extract witnesses from the existential in CanReachTarget
        var st0, final0 :| 0 <= st0 < |s| &&
                         s[st0] in {'G', 'T'} &&
                         (forall j :: 0 <= j < st0 ==> s[j] !in {'G', 'T'}) &&
                         st0 < final0 < |s| &&
                         s[final0] in {'G', 'T'} &&
                         (final0 - st0) % k == 0 &&
                         (forall pos :: st0 < pos < final0 && (pos - st0) % k == 0 ==> s[pos] !in {'G', 'T', '#'});
        // st0 and start are both indices of the first G/T, so they must be equal
        if start < st0 {
            // then s[start] is in {'G','T'} but start < st0 contradicts (forall j < st0 ==> no G/T)
            assert false;
        }
        if st0 < start {
            // then s[st0] in {'G','T'} but st0 < start contradicts (forall j < start ==> no G/T)
            assert false;
        }
        // hence st0 == start
        assert st0 == start;
        // Now final0 must be >= blockPos (since blockPos is the first multiple > start with a non-dot)
        // If final0 == blockPos then s[final0] == '#' contradicts s[final0] in {'G','T'}
        if final0 == blockPos {
            assert false;
        }
        // If final0 > blockPos then blockPos is between start and final0 and is a multiple, but s[blockPos] == '#'
        // contradicts the requirement that intermediate multiples are not in {'G','T','#'}
        if final0 > blockPos {
            // blockPos satisfies start < blockPos < final0 and (blockPos-start)%k==0
            assert false;
        }
        // No other possibility; contradiction established
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
    ensures not CanReachTarget(s, k)
{
    if CanReachTarget(s, k) {
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, s: string) returns (result: string)
    requires ValidInput(n, k, s)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanReachTarget(s, k)
// </vc-spec>
// <vc-code>
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
        assert start == start; assert final == final;
        assert 0 <= start < |s|;
        assert s[start] in {'G', 'T'};
        assert (forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'});
        // inner existential
        assert exists final0 ::
            start < final0 < |s| &&
            s[final0] in {'G', 'T'} &&
            (final0 - start) % k == 0 &&
            (forall pos :: start < pos < final0 && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'})
        by {
            // final0 = final
            assert start < final < |s|;
            assert s[final] in {'G', 'T'};
            assert (final - start) % k == 0;
            // positions between are '.' hence not in {'G','T','#'}
            assert forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'}
            by {
                reveal_forall;
                // from s[pos]=='.' we get s[pos] !in {'G','T','#'}
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
        // extract witnesses from the existential in CanReachTarget
        var st0, final0 :| 0 <= st0 < |s| &&
                         s[st0] in {'G', 'T'} &&
                         (forall j :: 0 <= j < st0 ==> s[j] !in {'G', 'T'}) &&
                         st0 < final0 < |s| &&
                         s[final0] in {'G', 'T'} &&
                         (final0 - st0) % k == 0 &&
                         (forall pos :: st0 < pos < final0 && (pos - st0) % k == 0 ==> s[pos] !in {'G', 'T', '#'});
        // st0 and start are both indices of the first G/T, so they must be equal
        if start < st0 {
            // then s[start] is in {'G','T'} but start < st0 contradicts (forall j < st0 ==> no G/T)
            assert false;
        }
        if st0 < start {
            // then s[st0] in {'G','T'} but st0 < start contradicts (forall j < start ==> no G/T)
            assert false;
        }
        // hence st0 == start
        assert st0 == start;
        // Now final0 must be >= blockPos (since blockPos is the first multiple > start with a non-dot)
        // If final0 == blockPos then s[final0] == '#' contradicts s[final0] in {'G','T'}
        if final0 == blockPos {
            assert false;
        }
        // If final0 > blockPos then blockPos is between start and final0 and is a multiple, but s[blockPos] == '#'
        // contradicts the requirement that intermediate multiples are not in {'G','T','#'}
        if final0 > blockPos {
            // blockPos satisfies start < blockPos < final0 and (blockPos-start)%k==0
            assert false;
        }
        // No other possibility; contradiction established
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
    ensures not CanReachTarget(s, k)
{
    if CanReachTarget(s, k) {
// </vc-code>

