method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
ensures a.Length == b.Length
ensures forall x :: 0 <= x < a.Length ==> b[x] == a[a.Length - x - 1]
// </vc-spec>
// <vc-code>
{
  b := new char[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: 0 <= x < i ==> b[x] == a[a.Length - x - 1]
  {
    b[i] := a[a.Length - i - 1];
    i := i + 1;
  }
}
// </vc-code>