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
lemma Lemma_FindFirstGOrT_Property(s: string, idx: int)
  requires exists i :: 0 <= i < |s| && s[i] in {'G', 'T'}
  requires 0 <= idx < |s|
  ensures FindFirstGOrT(s) <= idx
{
}

lemma Lemma_CanReachTarget_PositiveCase(s: string, k: int, start: int, final: int)
  requires k > 0
  requires 0 <= start < |s|
  requires start < final < |s|
  requires s[start] in {'G', 'T'}
  requires (final - start) % k == 0
  requires forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'}
  ensures CanReachTarget(s, k)
{
}

lemma Lemma_CharacterAtJumpPositions(s: string, k: int, start: int, final: int, pos: int)
  requires start < pos < final
  requires (pos - start) % k == 0
  requires forall p :: start < p < final && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'}
  ensures s[pos] !in {'G', 'T', '#'}
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
  var start := FindFirstGOrT(s);
  var current := start;
  
  while current < |s|
    invariant start <= current <= |s|
    invariant (current - start) % k == 0
    invariant s[start] in {'G', 'T'}
    invariant forall i :: 0 <= i < start ==> s[i] !in {'G', 'T'}
    invariant forall pos :: start < pos < current && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'}
  {
    if current >= |s| {
      break;
    }
    
    if s[current] == '#' {
      return "NO";
    }
    
    if s[current] in {'G', 'T'} && current > start {
      return "YES";
    }
    
    current := current + k;
  }
  
  return "NO";
}
// </vc-code>

