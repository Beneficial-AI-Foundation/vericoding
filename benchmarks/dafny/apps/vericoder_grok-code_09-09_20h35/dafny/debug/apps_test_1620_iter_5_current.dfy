predicate ValidInput(n: int)
{
  n >= 1
}

predicate ValidOutput(s: string, n: int)
{
  |s| == n &&
  (forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b' || s[i] == 'c') &&
  (forall i :: 0 <= i <= |s| - 3 ==> !(s[i] == s[i+2]))
}

predicate MinimalCUsage(s: string)
{
  forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
}

// <vc-helpers>
// <vc-helpers>
// No additional helpers needed, but invariants updated in code to aid verification
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
  requires ValidInput(n)
  ensures ValidOutput(result, n)
  ensures MinimalCUsage(result)
// </vc-spec>
// <vc-code>
{
  var chars := new char[n];
  if n >= 1 {
    chars[0] := 'a';
  }
  if n >= 2 {
    chars[1] := 'a';
  }
  if n >= 3 {
    for i := 2 to n - 1
      invariant forall j :: 0 <= j < i - 2 && j <= n - 3 ==> !(chars[j] == chars[j + 2])
      invariant forall j :: 0 <= j < i ==> chars[j] == 'a' || chars[j] == 'b'
    {
      chars[i] := if chars[i - 2] == 'a' then 'b' else 'a';
    }
  }
  var s := "";
  for i := 0 to n - 1
    invariant |s| == i && 0 <= i <= n
  {
    s := s + [chars[i]];
  }
  result := s;
}
// </vc-code>

