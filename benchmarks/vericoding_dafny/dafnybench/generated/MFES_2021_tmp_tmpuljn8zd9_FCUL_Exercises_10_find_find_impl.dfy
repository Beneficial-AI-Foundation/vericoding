method find(a: array<int>, key: int) returns(index: int)
    requires a.Length > 0;
    ensures 0 <= index <= a.Length;
    ensures index < a.Length ==> a[index] == key;
// </vc-spec>
// <vc-code>
{
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length;
    invariant forall i :: 0 <= i < index ==> a[i] != key;
  {
    if a[index] == key {
      return;
    }
    index := index + 1;
  }
}
// </vc-code>