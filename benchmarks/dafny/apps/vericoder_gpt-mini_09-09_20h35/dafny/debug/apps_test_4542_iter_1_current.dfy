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
  // Follows directly from the recursive definition of CountSegments.
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
    call CountSegmentsPrefix(s, i);
    segs := segs + add;
    i := i + 1;
    assert segs == CountSegments(s[..i]);
  }
  result := segs - 1;
}
// </vc-code>

