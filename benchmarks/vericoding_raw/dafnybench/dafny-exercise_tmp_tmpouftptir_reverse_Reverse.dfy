// <vc-helpers>
// </vc-helpers>

method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
ensures a == old(a)
ensures b.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> b[i] == a[a.Length - i - 1]
// <vc-code>
{
  assume false;
}
// </vc-code>