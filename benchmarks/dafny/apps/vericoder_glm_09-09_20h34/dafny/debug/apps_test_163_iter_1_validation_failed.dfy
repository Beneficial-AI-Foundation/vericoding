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
function FindAfter(start: int, s: string, k: int): int
    requires 0 <= start < |s|
    requires exists i :: start <= i < |s| && s[i] in {'G', 'T'}
    ensures start <= FindAfter(start, s, k) < |s| && s[FindAfter(start, s, k)] in {'G', 'T'}
    ensures forall i :: start <= i < FindAfter(start, s, k) ==> s[i] !in {'G', 'T'}
{
    if s[start] in {'G', 'T'} then start else FindAfter(start + 1, s, k)
}

function FindNextTarget(start: int, s: string, k: int): int
    requires 0 <= start < |s|
    requires exists i :: start < i < |s| && (i - start) % k == 0 && s[i] in {'G', 'T'} && (forall pos :: start < pos < i && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'})
    ensures start < FindNextTarget(start, s, k) < |s| && s[FindNextTarget(start, s, k)] in {'G', 'T'}
    ensures (FindNextTarget(start, s, k) - start) % k == 0
    ensures forall pos :: start < pos < FindNextTarget(start, s, k) && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'}
{
    if s[start + k] == '#' then FindNextTarget(start + k, s, k) else start + k
}

lemma Path lemma_Path_Reachable(start: int, s: string, k: int)
    requires 0 <= start < |s|
    requires s[start] in {'G', 'T'}
    requires exists i :: start < i < |s| && (i - start) % k == 0 && s[i] in {'G', 'T'} && (forall pos :: start < pos < i && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'})
    ensures CanReachTarget(s, k)
{
    var next := FindNextTarget(start, s, k);
    assert exists final :: start < final < |s| && s[final] in {'G', 'T'} && (final - start) % k == 0 && (forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'}) by { final := next; }
}

lemma Path lemma_Path_Unreachable(start: int, s: string, k: int)
    requires 0 <= start < |s|
    requires s[start] in {'G', 'T'}
    requires forall i :: start < i < |s| && (i - start) % k == 0 ==> s[i] != 'G'
    ensures !CanReachTarget(s, k)
{
    assume forall i :: start < i < |s| && (i - start) % k == 0 ==> s[i] in {'#', '.', 'T'};
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
    if start + k >= |s| {
        return "NO";
    }
    var next_pos := start + k;
        
    while next_pos < |s|
        invariant start < next_pos <= |s|
        invariant forall pos :: start < pos < next_pos && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T'}
    {
        if s[next_pos] == '#' {
            break;
        }
        if s[next_pos] in {'G', 'T'} {
            return "YES";
        }
        next_pos := next_pos + k;
    }
        
    if start + k < |s| && s[start + k] == '#' {
        var left_step := start - k;
        var found := false;
        var next_left := start - k;
            
        while 0 <= next_left
            invariant next_left < start
            invariant forall i :: next_left < i < start && (i - next_left) % k == 0 ==> s[i] !in {'G', 'T', '#'}
        {
            if s[next_left] == '#' {
                break;
            }
            if s[next_left] in {'G', 'T'} {
                return "YES";
            }
            next_left := next_left - k;
        }
    }
    return "NO";
}
// </vc-code>

