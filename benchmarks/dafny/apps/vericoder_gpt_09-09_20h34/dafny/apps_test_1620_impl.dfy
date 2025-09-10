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
  var res := "";
  while |res| < n
    invariant |res| <= n
    invariant forall i :: 0 <= i < |res| ==> res[i] == 'a' || res[i] == 'b'
    invariant forall i :: 0 <= i <= |res| - 3 ==> res[i] != res[i+2]
    decreases n - |res|
  {
    if |res| < 2 {
      res := res + "a";
    } else {
      if res[|res| - 2] == 'a' {
        res := res + "b";
      } else {
        res := res + "a";
      }
    }
  }
  result := res;
}
// </vc-code>

