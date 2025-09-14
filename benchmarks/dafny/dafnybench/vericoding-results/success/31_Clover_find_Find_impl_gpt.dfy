

// <vc-helpers>
// no helpers needed
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
    invariant forall j :: 0 <= j < i ==> a[j] != key
    decreases a.Length - i
  {
    if a[i] == key {
      index := i;
      return;
    }
    i := i + 1;
  }
  index := -1;
}
// </vc-code>

