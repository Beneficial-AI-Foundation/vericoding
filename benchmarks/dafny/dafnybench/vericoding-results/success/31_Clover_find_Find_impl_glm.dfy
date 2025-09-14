

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Find(a: array<int>, key: int) returns (index: int)
  ensures -1<=index<a.Length
  ensures index!=-1 ==> a[index]==key && (forall i :: 0 <= i < index ==> a[i] != key)
  ensures index == -1 ==> (forall i::0 <= i < a.Length ==> a[i] != key)
// </vc-spec>
// <vc-code>
{
  var i: int := 0;
  while i < a.Length && a[i] != key
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] != key
  {
    i := i + 1;
  }
  if i < a.Length {
    return i;
  } else {
    return -1;
  }
}
// </vc-code>

