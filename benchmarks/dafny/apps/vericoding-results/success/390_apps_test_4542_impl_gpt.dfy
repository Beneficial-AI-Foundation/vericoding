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
lemma CountSegments_Extend(s: string, k: nat)
  requires 1 <= k < |s|
  ensures CountSegments(s[..k+1]) == CountSegments(s[..k]) + (if s[k] != s[k-1] then 1 else 0)
{
  var t := s[..k+1];
  assert |t| == k + 1;
  assert |t| >= 2;
  assert CountSegments(t) == CountSegments(t[..|t|-1]) + (if t[|t|-1] != t[|t|-2] then 1 else 0);
  assert t[..|t|-1] == s[..k];
  assert t[|t|-1] == s[k];
  assert t[|t|-2] == s[k-1];
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
  result := 0;
  var i := 1;
  assert |s[..1]| == 1;
  assert CountSegments(s[..1]) == 1;
  while i < n
    invariant 1 <= i <= n
    invariant result == CountSegments(s[..i]) - 1
  {
    if s[i] != s[i - 1] {
      CountSegments_Extend(s, i);
      result := result + 1;
      assert result == CountSegments(s[..i+1]) - 1;
    } else {
      CountSegments_Extend(s, i);
      assert result == CountSegments(s[..i+1]) - 1;
    }
    i := i + 1;
    assert result == CountSegments(s[..i]) - 1;
  }
  assert s[..n] == s;
  assert result == CountSegments(s) - 1;
}
// </vc-code>

