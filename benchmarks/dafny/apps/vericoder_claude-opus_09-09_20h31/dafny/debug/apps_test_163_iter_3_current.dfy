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
lemma FindFirstGOrTCorrect(s: string)
    requires exists i :: 0 <= i < |s| && s[i] in {'G', 'T'}
    ensures 0 <= FindFirstGOrT(s) < |s|
    ensures s[FindFirstGOrT(s)] in {'G', 'T'}
    ensures forall j :: 0 <= j < FindFirstGOrT(s) ==> s[j] !in {'G', 'T'}
{
    var idx := FindFirstGOrT(s);
    if s[0] in {'G', 'T'} {
        assert idx == 0;
    } else {
        assert idx == FindFirstGOrT(s[1..]) + 1;
        FindFirstGOrTCorrect(s[1..]);
    }
}

lemma CanReachTargetDefinition(s: string, k: int, start: int, final: int)
    requires k > 0
    requires 0 <= start < final < |s|
    requires s[start] in {'G', 'T'}
    requires s[final] in {'G', 'T'}
    requires forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'}
    requires (final - start) % k == 0
    requires forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'}
    ensures CanReachTarget(s, k)
{
    // The witness directly satisfies the definition
}

lemma NoTargetFound(s: string, k: int, start: int, n: int)
    requires k > 0
    requires 0 <= start < n <= |s|
    requires s[start] in {'G', 'T'}
    requires forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'}
    requires forall final :: start < final < n && s[final] in {'G', 'T'} && (final - start) % k == 0 ==>
        exists pos :: start < pos < final && (pos - start) % k == 0 && s[pos] in {'G', 'T', '#'}
    ensures !CanReachTarget(s, k)
{
    if CanReachTarget(s, k) {
        // There must be a witness
        var witness_start :| 0 <= witness_start < |s| && s[witness_start] in {'G', 'T'} &&
            (forall j :: 0 <= j < witness_start ==> s[j] !in {'G', 'T'}) &&
            (exists final :: witness_start < final < |s| && s[final] in {'G', 'T'} &&
                (final - witness_start) % k == 0 &&
                (forall pos :: witness_start < pos < final && (pos - witness_start) % k == 0 ==> s[pos] !in {'G', 'T', '#'}));
        
        // Since witness_start is the first G or T, it must equal start
        assert witness_start == start;
        
        var witness_final :| witness_start < witness_final < |s| && s[witness_final] in {'G', 'T'} &&
            (witness_final - witness_start) % k == 0 &&
            (forall pos :: witness_start < pos < witness_final && (pos - witness_start) % k == 0 ==> s[pos] !in {'G', 'T', '#'});
        
        // If witness_final < n, our precondition says there's an obstacle
        if witness_final < n {
            assert exists pos :: start < pos < witness_final && (pos - start) % k == 0 && s[pos] in {'G', 'T', '#'};
            // This contradicts the witness property
            assert false;
        } else {
            // witness_final >= n, but we checked all positions up to n
            // This can't happen as we checked exhaustively
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
    FindFirstGOrTCorrect(s);
    
    var pos := start + k;
    
    while pos < n
        invariant start + k <= pos <= n
        invariant (pos - start) % k == 0
        invariant forall final :: start < final < pos && s[final] in {'G', 'T'} && (final - start) % k == 0 ==>
            exists p :: start < p < final && (p - start) % k == 0 && s[p] in {'G', 'T', '#'}
    {
        if s[pos] in {'G', 'T'} {
            var checkPos := start + k;
            var blocked := false;
            
            while checkPos < pos
                invariant start + k <= checkPos <= pos
                invariant (checkPos - start) % k == 0
                invariant !blocked ==> forall p :: start < p < checkPos && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'}
                invariant blocked ==> exists p :: start < p < pos && (p - start) % k == 0 && s[p] in {'G', 'T', '#'}
            {
                if s[checkPos] in {'G', 'T', '#'} {
                    blocked := true;
                    break;
                }
                checkPos := checkPos + k;
            }
            
            if !blocked {
                CanReachTargetDefinition(s, k, start, pos);
                result := "YES";
                return;
            }
        }
        pos := pos + k;
    }
    
    NoTargetFound(s, k, start, n);
    result := "NO";
}
// </vc-code>

