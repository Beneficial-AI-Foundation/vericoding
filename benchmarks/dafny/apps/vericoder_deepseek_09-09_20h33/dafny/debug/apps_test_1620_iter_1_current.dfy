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
lemma LemmaEvenOddPattern(n: int, i: int)
  requires n >= 1
  requires 0 <= i < n
  ensures (i % 2 == 0) ==> (i % 2 != 1)
  ensures (i % 2 == 1) ==> (i % 2 != 0)
{
}

lemma LemmaNoABCForbiddenPattern(s: string, n: int)
  requires |s| == n
  requires forall i :: 0 <= i < n ==> s[i] == 'a' || s[i] == 'b'
  requires forall i :: 0 <= i < n ==> i % 2 == 0 ==> s[i] == s[0]
  requires forall i :: 0 <= i < n ==> i % 2 == 1 ==> s[i] == s[1]
  ensures ValidOutput(s, n)
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
  requires ValidInput(n)
  ensures ValidOutput(result, n)
  ensures MinimalCUsage(result)
// </vc-spec>
// <vc-code>
{
  var s := new char[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> s[j] == 'a' || s[j] == 'b'
    invariant forall j :: 0 <= j < i ==> j % 2 == 0 ==> s[j] == s[0]
    invariant forall j :: 0 <= j < i ==> j % 2 == 1 ==> s[j] == s[1]
  {
    if i % 2 == 0 {
      s[i] := 'a';
    } else {
      s[i] := 'b';
    }
    i := i + 1;
  }
  result := s[0..n];
  assert ValidOutput(result, n);
  assert MinimalCUsage(result);
}
// </vc-code>

