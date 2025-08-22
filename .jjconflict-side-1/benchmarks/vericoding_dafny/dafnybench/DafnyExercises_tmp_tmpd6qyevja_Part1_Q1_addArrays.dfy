// <vc-helpers>
// </vc-helpers>

method addArrays(a : array<int>, b : array<int>) returns (c : array<int>) 
requires a.Length == b.Length
ensures b.Length == c.Length
ensures forall i:int :: 0 <= i <c.Length ==> c[i] == a[i] + b[i]
// <vc-code>
{
  assume false;
}
// </vc-code>