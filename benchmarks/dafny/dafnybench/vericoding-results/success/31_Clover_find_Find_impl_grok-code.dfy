

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Find(a: array<int>, key: int) returns (index: int)
  ensures -1<=index<a.Length
  ensures index!=-1 ==> a[index]==key && (forall i :: 0 <= i < index ==> a[i] != key)
  ensures index == -1 ==> (forall i::0 <= i < a.Length ==> a[i] != key)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length 
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != key
  {
    if a[i] == key {
      return i;
    }
    i := i + 1;
  }
  return -1;
}
// </vc-code>

