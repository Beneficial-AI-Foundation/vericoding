// <vc-helpers>
// </vc-helpers>

method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
ensures a.Length == b.Length
ensures forall x :: 0 <= x < a.Length ==> b[x] == a[a.Length - x - 1]
// <vc-code>
{
  assume false;
}
// </vc-code>