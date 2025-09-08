Given a line of n cells and a grasshopper that can jump exactly k cells at a time,
determine if the grasshopper can reach a target cell. The line contains exactly one
grasshopper ('G'), one target ('T'), empty cells ('.'), and obstacles ('#').
The grasshopper can only land on empty cells or the target.

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

method solve(n: int, k: int, s: string) returns (result: string)
    requires ValidInput(n, k, s)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanReachTarget(s, k)
{
    // Find first G or T
    var start := 0;
    while start < |s| && s[start] !in {'G', 'T'}
        invariant 0 <= start <= |s|
        invariant forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'}
    {
        start := start + 1;
    }

    if start >= |s| {
        result := "NO";
        return;
    }

    // Jump k positions at a time
    var pos := start + k;

    while pos < |s| && s[pos] !in {'G', 'T', '#'}
        invariant start + k <= pos
        invariant (pos - start) % k == 0
        invariant forall p :: start < p < pos && (p - start) % k == 0 && p < |s| ==> s[p] !in {'G', 'T', '#'}
        invariant start < |s| && s[start] in {'G', 'T'}
        invariant forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'}
    {
        pos := pos + k;
    }

    if pos < |s| && s[pos] in {'G', 'T'} {
        result := "YES";
    } else {
        result := "NO";
    }
}
