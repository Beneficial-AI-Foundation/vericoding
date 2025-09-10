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
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
  requires ValidInput(n)
  ensures ValidOutput(result, n)
  ensures MinimalCUsage(result)
// </vc-spec>
// <vc-code>
{
  var result := new char[n];
  if n >= 1 {
    result[0] := 'a';
  }
  if n >= 2 {
    result[1] := 'a';
  }
  for i := 2 to n - 1
  {
    result[i] := if result[i - 2] == 'a' then 'b' else 'a';
  }
  var s := "";
  for i := 0 to n - 1
  {
    s := s + [result[i]];
  }
  result := s;
}
// </vc-code>

