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
    {
        if s[pos] in {'G', 'T'} {
            // Check if path is clear
            var checkPos := start + k;
            var pathClear := true;
            
            while checkPos < pos
                invariant start + k <= checkPos <= pos
                invariant (checkPos - start) % k == 0
                invariant pathClear ==> forall p :: start < p < checkPos && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'}
            {
                if s[checkPos] in {'G', 'T', '#'} {
                    pathClear := false;
                    break;
                }
                checkPos := checkPos + k;
            }
            
            if pathClear {
                // We found a valid path
                assert s[start] in {'G', 'T'};
                assert s[pos] in {'G', 'T'};
                assert (pos - start) % k == 0;
                assert forall p :: start < p < pos && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'};
                assert forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'};
                assert CanReachTarget(s, k);
                result := "YES";
                return;
            }
        }
        pos := pos + k;
    }
    
    // No valid path found
    assert !CanReachTarget(s, k);
    result := "NO";
}
// </vc-code>

