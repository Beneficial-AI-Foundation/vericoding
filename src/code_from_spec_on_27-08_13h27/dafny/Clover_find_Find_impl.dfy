// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Find(a: array<int>, key: int) returns (index: int)
  ensures -1<=index<a.Length
  ensures index!=-1 ==> a[index]==key && (forall i :: 0 <= i < index ==> a[i] != key)
  ensures index == -1 ==> (forall i::0 <= i < a.Length ==> a[i] != key)
// </vc-spec>
// </vc-spec>

// <vc-code>
method FindImpl(a: array<int>, key: int) returns (index: int)
  ensures -1 <= index < a.Length
  ensures index != -1 ==> a[index] == key && (forall i :: 0 <= i < index ==> a[i] != key)
  ensures index == -1 ==> (forall i :: 0 <= i < a.Length ==> a[i] != key)
{
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall i :: 0 <= i < index ==> a[i] != key
  {
    if a[index] == key {
      return index;
    }
    index := index + 1;
  }
  return -1;
}
// </vc-code>
