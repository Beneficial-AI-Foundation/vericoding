

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
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
    invariant forall j :: 0 <= j < i ==> c[j] == a[j]
  {
    c[i] := a[i];
    i := i + 1;
  }
  
  var k := 0;
  while k < b.Length
    invariant 0 <= k <= b.Length
    invariant forall j :: 0 <= j < a.Length ==> c[j] == a[j]
    invariant forall j :: 0 <= j < k ==> c[a.Length + j] == b[j]
  {
    c[a.Length + k] := b[k];
    k := k + 1;
  }
}
// </vc-code>

