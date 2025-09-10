predicate ValidInput(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] == 'B' || s[i] == 'W'
}

function CountSegments(s: string): int
    requires |s| > 0
    ensures CountSegments(s) >= 1
    ensures CountSegments(s) <= |s|
{
    if |s| == 1 then 1
    else 
        CountSegments(s[..|s|-1]) + (if s[|s|-1] != s[|s|-2] then 1 else 0)
}

// <vc-helpers>
lemma CountSegmentsPrefix(s: string, n: int)
  requires 1 <= n < |s|
  ensures CountSegments(s[..n+1]) == CountSegments(s[..n]) + (if s[n] != s[n-1] then 1 else 0)
{
  // length of the prefix s[..n+1] is n+1
  assert |s[..n+1]| == n+1;
  // since n >= 1, n+1 > 1, so by the definition of CountSegments on s[..n+1] we get the recursive form
  assert CountSegments(s[..n+1]) ==
    CountSegments((s[..n+1])[..|s[..n+1]| - 1]) + (if (s[..n+1])[|s[..n+1]| - 1] != (s[..n+1])[|s[..n+1]| - 2] then 1 else 0);
  // simplify the slices and indices to relate them to s[..n] and s[n], s[n-1]
  assert (s[..n+1])[..|s[..n+1]| - 1] == s[..n];
  assert (s[..n+1])[|s[..n+1]| - 1] == s[n];
  assert (s[..n+1])[|s[..n+1]| - 2] == s[n-1];
  assert CountSegments((s[..n+1])[..|s[..n+1]| - 1]) == CountSegments(s[..n]);
  assert (if (s[..n+1])[|s[..n+1]| - 1] != (s[..n+1])[|s[..n+1]| - 2] then 1 else 0) == (if s[n] != s[n-1] then 1 else 0);
  // conclude the desired equality
  assert CountSegments(s[..n+1]) == CountSegments(s[..n]) + (if s[n] != s[n-1] then 1 else 0);
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result >= 0
    ensures result == CountSegments(s) - 1
    ensures result <= |s| - 1
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  var segs := 1;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant 1 <= segs <= i
    invariant segs == CountSegments(s[..i])
  {
    var add := if s[i] != s[i-1] then 1 else 0;
    CountSegmentsPrefix(s, i);
    segs := segs + add;
    i := i + 1;
    assert segs == CountSegments(s[..i]);
  }
  result := segs - 1;
}
// </vc-code>

