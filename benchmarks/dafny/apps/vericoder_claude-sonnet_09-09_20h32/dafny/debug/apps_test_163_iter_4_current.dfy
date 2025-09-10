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
    ensures var pos := FindFirstGOrT(s); 0 <= pos < |s| && s[pos] in {'G', 'T'}
    ensures forall j :: 0 <= j < FindFirstGOrT(s) ==> s[j] !in {'G', 'T'}
{
    if s[0] in {'G', 'T'} {
        // Base case
    } else {
        FindFirstGOrTCorrect(s[1..]);
    }
}

function FindTarget(s: string, start: int): int
    requires 0 <= start < |s|
    requires s[start] in {'G', 'T'}
    requires exists i :: start < i < |s| && s[i] in {'G', 'T'}
    decreases |s| - start
{
    if start + 1 < |s| && s[start + 1] in {'G', 'T'} then start + 1
    else if start + 1 < |s| then 
        assert exists i :: start + 1 < i < |s| && s[i] in {'G', 'T'};
        FindTarget(s, start + 1)
    else start + 1 // This case won't happen due to precondition, but needed for totality
}

lemma FindTargetCorrect(s: string, start: int)
    requires 0 <= start < |s|
    requires s[start] in {'G', 'T'}
    requires exists i :: start < i < |s| && s[i] in {'G', 'T'}
    ensures var target := FindTarget(s, start); start < target < |s| && s[target] in {'G', 'T'}
    ensures forall j :: start < j < FindTarget(s, start) ==> s[j] !in {'G', 'T'}
    decreases |s| - start
{
    if start + 1 < |s| && s[start + 1] in {'G', 'T'} {
        // Base case
    } else if start + 1 < |s| {
        assert exists i :: start + 1 < i < |s| && s[i] in {'G', 'T'};
        FindTargetCorrect(s, start + 1);
    }
}

predicate CanJumpToTarget(s: string, start: int, target: int, k: int)
    requires 0 <= start < target < |s|
    requires k > 0
{
    (target - start) % k == 0 &&
    (forall pos :: start < pos < target && (pos - start) % k == 0 ==> pos < |s| && s[pos] !in {'G', 'T', '#'})
}

lemma HelperCanReach(s: string, start: int, target: int, k: int)
    requires 0 <= start < target < |s|
    requires s[start] in {'G', 'T'}
    requires s[target] in {'G', 'T'}
    requires forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'}
    requires forall j :: start < j < target ==> s[j] !in {'G', 'T'}
    requires CanJumpToTarget(s, start, target, k)
    requires k > 0
    ensures CanReachTarget(s, k)
{
    assert exists start_pos :: 
        0 <= start_pos < |s| && 
        s[start_pos] in {'G', 'T'} &&
        (forall j :: 0 <= j < start_pos ==> s[j] !in {'G', 'T'}) &&
        (exists final :: 
            start_pos < final < |s| &&
            s[final] in {'G', 'T'} &&
            (final - start_pos) % k == 0 &&
            (forall pos :: start_pos < pos < final && (pos - start_pos) % k == 0 ==> s[pos] !in {'G', 'T', '#'})
        ) by {
        var start_pos := start;
        var final := target;
        assert start_pos == start && final == target;
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
    assert k > 0;
    FindFirstGOrTCorrect(s);
    var start := FindFirstGOrT(s);
    
    assert exists i :: start < i < |s| && s[i] in {'G', 'T'} by {
        assert exists i :: 0 <= i < |s| && s[i] == 'G';
        assert exists i :: 0 <= i < |s| && s[i] == 'T';
        assert forall i, j :: 0 <= i < j < |s| && s[i] == 'G' ==> s[j] != 'G';
        assert forall i, j :: 0 <= i < j < |s| && s[i] == 'T' ==> s[j] != 'T';
    }
    
    FindTargetCorrect(s, start);
    var target := FindTarget(s, start);
    
    if (target - start) % k != 0 {
        result := "NO";
        return;
    }
    
    var pos := start + k;
    while pos < target
        invariant start < pos <= target
        invariant (pos - start) % k == 0
        invariant forall p :: start < p < pos && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'}
    {
        if s[pos] in {'G', 'T', '#'} {
            result := "NO";
            return;
        }
        pos := pos + k;
    }
    
    assert CanJumpToTarget(s, start, target, k);
    assert forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'};
    assert forall j :: start < j < target ==> s[j] !in {'G', 'T'};
    HelperCanReach(s, start, target, k);
    result := "YES";
}
// </vc-code>

