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

// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
  requires ValidInput(n)
  ensures ValidOutput(result, n)
  ensures MinimalCUsage(result)
// </vc-spec>
// <vc-code>
{
  var s := "";
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |s| == i
    invariant forall j :: 0 <= j < |s| ==> s[j] == 'a' || s[j] == 'b'
    invariant forall j :: 0 <= j <= |s| - 3 ==> !(s[j] == s[j+2])
    decreases n - i
  {
    if i >= 2 {
      if s[i - 2] == 'a' {
        s := s + "b";
      } else {
        assert s[i - 2] == 'b';
        s := s + "a";
      }
    } else {
      s := s + "a";
    }
    i := i + 1;
  }
  return s;
}
// </vc-code>

