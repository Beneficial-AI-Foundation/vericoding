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
// (No helpers needed for this solution)
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
  requires ValidInput(n)
  ensures ValidOutput(result, n)
  ensures MinimalCUsage(result)
// </vc-spec>
// <vc-code>
{
  var a := new char[n];
  if n >= 1 {
    a[0] := 'a';
  }
  if n >= 2 {
    a[1] := 'a';
  }
  var i := 2;
  if i > n { i := n; }
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == 'a' || a[j] == 'b'
    invariant forall j :: 0 <= j <= i - 3 ==> a[j] != a[j+2]
  {
    if a[i-2] == 'a' {
      a[i] := 'b';
    } else {
      a[i] := 'a';
    }
    i := i + 1;
  }
  result := a[..];
  assert |result| == n;
  assert forall j :: 0 <= j < n ==> result[j] == a[j];
  assert forall j :: 0 <= j < n ==> result[j] == 'a' || result[j] == 'b';
  assert forall j :: 0 <= j <= n - 3 ==> !(result[j] == result[j+2]);
}
// </vc-code>

