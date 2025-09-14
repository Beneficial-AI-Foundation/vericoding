predicate triple(a: array<int>) 
reads a
{
    exists i :: 0 <= i < a.Length - 2 && a[i] == a[i + 1] == a[i + 2]
}

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method GetTriple(a: array<int>) returns (index: int)
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures index == a.Length <==> !triple(a)
ensures 0 <= index < a.Length - 2 <==> triple(a)
ensures 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2]
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i <= a.Length - 3
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i && k + 2 < a.Length ==> !(a[k] == a[k+1] && a[k+1] == a[k+2])
    decreases a.Length - i
  {
    if a[i] == a[i+1] && a[i+1] == a[i+2] {
      index := i;
      return;
    }
    i := i + 1;
  }
  index := a.Length;
}
// </vc-code>

