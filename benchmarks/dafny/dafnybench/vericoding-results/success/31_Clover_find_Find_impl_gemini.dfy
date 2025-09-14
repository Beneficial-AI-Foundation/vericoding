// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate NotFoundBefore(a: array<int>, key: int, limit: int) reads a requires 0 <= limit <= a.Length { forall i :: 0 <= i < limit ==> a[i] != key }
// </vc-helpers>

// <vc-spec>
method Find(a: array<int>, key: int) returns (index: int)
  ensures -1<=index<a.Length
  ensures index!=-1 ==> a[index]==key && (forall i :: 0 <= i < index ==> a[i] != key)
  ensures index == -1 ==> (forall i::0 <= i < a.Length ==> a[i] != key)
// </vc-spec>
// <vc-code>
{
  index := -1;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant index == -1
    invariant forall k :: 0 <= k < i ==> a[k] != key
  {
    if a[i] == key {
      index := i;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
