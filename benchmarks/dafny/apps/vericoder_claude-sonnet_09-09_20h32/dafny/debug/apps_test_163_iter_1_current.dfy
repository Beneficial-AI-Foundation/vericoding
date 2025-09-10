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
{
    if start + 1 < |s| && s[start + 1] in {'G', 'T'} then start + 1
    else FindTarget(s, start + 1)
}

lemma FindTargetCorrect(s: string, start: int)
    requires 0 <= start < |s|
    requires s[start] in {'G', 'T'}
    requires exists i :: start < i < |s| && s[i] in {'G', 'T'}
    ensures var target := FindTarget(s, start); start < target < |s| && s[target] in {'G', 'T'}
    ensures forall j :: start < j < FindTarget(s, start) ==> s[j] !in {'G', 'T'}
{
    if start + 1 < |s| && s[start + 1] in {'G', 'T'} {
        // Base case
    } else {
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
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, s: string) returns (result: string)
    requires ValidInput(n, k, s)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanReachTarget(s, k)
// </vc-spec>
// <vc-code>
{
    FindFirstGOrTCorrect(s);
    var start := FindFirstGOrT(s);
    
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
    
    result := "YES";
}
// </vc-code>

