method appendArray(a: array<int>, b: array<int>) returns (c: array<int>)
ensures c.Length == a.Length + b.Length
ensures forall i :: 0 <= i < a.Length ==> a[i] == c[i]
ensures forall i :: 0 <= i < b.Length ==> b[i] == c[a.Length + i]
// </vc-spec>
// <vc-code>
{
  c := new int[a.Length + b.Length];
  
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] == c[j]
  {
    c[i] := a[i];
    i := i + 1;
  }
  
  var j := 0;
  while j < b.Length
    invariant 0 <= j <= b.Length
    invariant forall k :: 0 <= k < a.Length ==> a[k] == c[k]
    invariant forall k :: 0 <= k < j ==> b[k] == c[a.Length + k]
  {
    c[a.Length + j] := b[j];
    j := j + 1;
  }
}
// </vc-code>