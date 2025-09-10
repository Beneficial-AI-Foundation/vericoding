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
method FindFirstGOrTIter(s: string) returns (res: int)
  requires exists i :: 0 <= i < |s| && s[i] in {'G', 'T'}
{
  var i := 0;
  while true
  {
    if i >= |s| { assume false; }
    if s[i] in {'G', 'T'} { return i; }
    i := i + 1;
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
  var posG, posT := -1, -1;
  for i := 0 to n-1
  {
    if s[i] == 'G' { posG := i; }
    if s[i] == 'T' { posT := i; }
  }
  var start := FindFirstGOrTIter(s);
  var final: int;
  if s[start] == 'G' {
    final := posT;
  } else {
    final := posG;
  }
  if final <= start || (final - start) % k != 0 {
    result := "NO";
  } else {
    var can := true;
    var pos := start + k;
    while pos < final
      invariant pos > start
      invariant (pos - start) % k == 0
      decreases final - pos
    {
      if s[pos] != '.' {
        can := false;
      }
      pos := pos + k;
    }
    if can {
      result := "YES";
    } else {
      result := "NO";
    }
  }
}
// </vc-code>

