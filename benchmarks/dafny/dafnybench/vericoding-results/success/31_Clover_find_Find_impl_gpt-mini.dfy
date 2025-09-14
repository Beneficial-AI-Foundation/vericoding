

// <vc-helpers>
// No helpers needed.
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
  index := -1;
  while i < a.Length && index == -1
    decreases if index == -1 then a.Length - i else 0
    invariant -1 <= index < a.Length
    invariant 0 <= i <= a.Length
    invariant index == -1 ==> (forall j :: 0 <= j < i ==> a[j] != key)
    invariant index != -1 ==> a[index] == key && (forall j :: 0 <= j < index ==> a[j] != key)
  {
    if a[i] == key {
      index := i;
    } else {
      i := i + 1;
    }
  }
  if index == -1 {
    assert i == a.Length;
  } else {
    assert a[index] == key;
  }
}
// </vc-code>

