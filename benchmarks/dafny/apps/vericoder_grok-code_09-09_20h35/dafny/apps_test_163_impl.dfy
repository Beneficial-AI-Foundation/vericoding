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
function FindG(s: string): int
  requires exists i :: 0 <= i < |s| && s[i] == 'G'
  decreases |s|
{
  if s[0] == 'G' then 0 else FindG(s[1..]) + 1
}

function FindT(s: string): int
  requires exists i :: 0 <= i < |s| && s[i] == 'T'
  decreases |s|
{
  if s[0] == 'T' then 0 else FindT(s[1..]) + 1
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
  var p_G := FindG(s);
  var p_T := FindT(s);
  var start : int;
  var other : int;
  if p_G < p_T {
    start := p_G;
    other := p_T;
  } else {
    start := p_T;
    other := p_G;
  }
  if (other - start) % k != 0 {
    return "NO";
  }
  var current := start + k;
  while current < other
    invariant current >= start + k
    invariant current <= |s|
    invariant (current - start) % k == 0
    invariant forall pos :: start <= pos < current && (pos - start) % k == 0 ==> s[pos] == '.'
  {
    if s[current] != '.' {
      return "NO";
    }
    current := current + k;
  }
  return "YES";
}
// </vc-code>

