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
predicate {:opaque} IsReachable(s: string, k: int, start: int, current: int, final: int)
    requires 0 <= start < current < final < |s|
    requires s[start] in {'G', 'T'}
    requires s[final] in {'G', 'T'}
    requires (final - start) % k == 0
{
    (current - start) % k == 0 && s[current] !in {'G', 'T', '#'}
}

function FindNextValidPosition(s: string, k: int, start: int, current: int, final: int): int
    requires 0 <= start < current < final < |s|
    requires s[start] in {'G', 'T'}
    requires s[final] in {'G', 'T'}
    requires (final - start) % k == 0
    decreases final - current
    returns (next_pos: int)
    ensures next_pos == -1 || (current < next_pos < final && (next_pos - start) % k == 0)
{
    var next_candidate := current + k;
    if next_candidate >= final then
        -1 // No more valid positions before 'final'
    else if (next_candidate - start) % k == 0 then
        next_candidate
    else // This branch is technically not reachable given the premise (next_candidate = current + k)
        // unless k itself is not well behaved. But next_candidate is an integer.
        -1
}

lemma {:induction current} LemmaCheckPath(s: string, k: int, start: int, current: int, final: int)
    requires 0 <= start < current < final < |s|
    requires s[start] in {'G', 'T'}
    requires s[final] in {'G', 'T'}
    requires (final - start) % k == 0
    requires (current - start) % k == 0
    requires (forall pos :: start < pos < current && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'})
    ensures s[current] !in {'G', 'T', '#'} ==> (forall pos :: start < pos <= current && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'})
{
    // The inductive hypothesis already covers the range start < pos < current.
    // We just need to ensure s[current] is checked.
}

predicate IsClearPath(s: string, k: int, start: int, final: int)
    requires 0 <= start < final < |s|
    requires s[start] in {'G', 'T'}
    requires s[final] in {'G', 'T'}
    requires (final - start) % k == 0
{
    forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'}
}

lemma IsClearPathHolds(s: string, k: int, start: int, final: int)
    requires 0 <= start < final < |s|
    requires s[start] in {'G', 'T'}
    requires s[final] in {'G', 'T'}
    requires (final - start) % k == 0
    // If the loop finds no '#' or 'G'/'T' at intermediate steps, this lemma ensures IsClearPath.
    ensures (forall pos :: start < pos < final && (pos - start) % k == 0 && s[pos] in {'G', 'T', '#'} ==> false) ==> IsClearPath(s, k, start, final)
{
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
    var str_len := n;
    var g_pos: int := -1;
    var t_pos: int := -1;

    for i := 0 to str_len - 1
        invariant 0 <= i <= str_len
        invariant g_pos == -1 || (0 <= g_pos < i && s[g_pos] == 'G')
        invariant t_pos == -1 || (0 <= t_pos < i && s[t_pos] == 'T')
        invariant (g_pos != -1 && t_pos != -1) ==> (forall j, l :: 0 <= j < l < i && s[j] == 'G' ==> s[l] != 'G')
        invariant (g_pos != -1 && t_pos != -1) ==> (forall j, l :: 0 <= j < l < i && s[j] == 'T' ==> s[l] != 'T')
    {
        if s[i] == 'G' {
            g_pos := i;
        } else if s[i] == 'T' {
            t_pos := i;
        }
    }

    // ValidInput ensures that there is exactly one 'G' and one 'T'.
    // So g_pos and t_pos will be set from the loop.

    // Check G -> T
    if g_pos < t_pos && ((t_pos - g_pos) % k == 0) {
        var possible := true;
        var current_pos := g_pos + k;
        while possible && current_pos < t_pos
            invariant g_pos < current_pos <= t_pos
            invariant (current_pos - g_pos) % k == 0
            invariant forall pos :: g_pos < pos < current_pos && (pos - g_pos) % k == 0 ==> s[pos] !in {'G', 'T', '#'}
        {
            if s[current_pos] in {'G', 'T', '#'} {
                possible := false;
            }
            current_pos := current_pos + k;
        }
        if possible {
            return "YES";
        }
    }

    // Check T -> G
    if t_pos < g_pos && ((g_pos - t_pos) % k == 0) {
        var possible := true;
        var current_pos := t_pos + k;
        while possible && current_pos < g_pos
            invariant t_pos < current_pos <= g_pos
            invariant (current_pos - t_pos) % k == 0
            invariant forall pos :: t_pos < pos < current_pos && (pos - t_pos) % k == 0 ==> s[pos] !in {'G', 'T', '#'}
        {
            if s[current_pos] in {'G', 'T', '#'} {
                possible := false;
            }
            current_pos := current_pos + k;
        }
        if possible {
            return "YES";
        }
    }

    return "NO";
}
// </vc-code>

