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

lemma CanReachTargetImpliesFoundPath(s: string, k: int)
    requires k > 0
    requires CanReachTarget(s, k)
    ensures exists start, final :: 
        0 <= start < final < |s| &&
        s[start] in {'G', 'T'} &&
        s[final] in {'G', 'T'} &&
        (forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'}) &&
        (final - start) % k == 0 &&
        (forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'})
{
    // This follows directly from the definition of CanReachTarget
}

lemma PathFoundImpliesCanReachTarget(s: string, k: int, start: int, final: int)
    requires k > 0
    requires 0 <= start < final < |s|
    requires s[start] in {'G', 'T'}
    requires s[final] in {'G', 'T'}
    requires (final - start) % k == 0
    requires forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'}
    requires forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'}
    ensures CanReachTarget(s, k)
{
    // Directly construct the witness
    assert CanReachTarget(s, k);
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
    // Find the starting position (first G or T)
    var start := FindFirstGOrT(s);
    FindFirstGOrTCorrect(s);
    
    // Look for a reachable target
    var found := false;
    var pos := start + k;
    
    while pos < n && !found
        invariant start < n
        invariant start + k <= pos <= n + k
        invariant (pos - start) % k == 0
        invariant found ==> CanReachTarget(s, k)
        invariant !found ==> forall final :: start < final < pos && final < n && s[final] in {'G', 'T'} && (final - start) % k == 0 ==> 
            !(forall p :: start < p < final && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'})
    {
        if pos < n && s[pos] in {'G', 'T'} {
            // Check if path is clear
            var pathClear := true;
            var checkPos := start + k;
            
            while checkPos < pos && pathClear
                invariant start + k <= checkPos <= pos
                invariant (checkPos - start) % k == 0
                invariant pathClear ==> forall p :: start < p < checkPos && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'}
            {
                if s[checkPos] in {'G', 'T', '#'} {
                    pathClear := false;
                } else {
                    checkPos := checkPos + k;
                }
            }
            
            if pathClear {
                found := true;
                PathFoundImpliesCanReachTarget(s, k, start, pos);
            }
        }
        
        if !found && pos + k <= n {
            pos := pos + k;
        } else if !found {
            break;
        }
    }
    
    if found {
        result := "YES";
    } else {
        result := "NO";
        // Prove that if not found, then CanReachTarget(s, k) is false
        if CanReachTarget(s, k) {
            CanReachTargetImpliesFoundPath(s, k);
            // This gives us a witness that should have been found
            assert false; // Contradiction
        }
    }
}
// </vc-code>

