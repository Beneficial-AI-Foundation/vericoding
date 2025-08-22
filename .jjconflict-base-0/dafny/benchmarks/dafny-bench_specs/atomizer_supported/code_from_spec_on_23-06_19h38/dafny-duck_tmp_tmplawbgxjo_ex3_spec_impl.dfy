// ATOM 
predicate sortedbad(s: string)
{
  // no b's after non-b's
  (forall i, j :: 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b' ==> i < j) &&
  // only non-d's before d's
  (forall i, j :: 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd' ==> i < j)
}

//IMPL BadSort
method BadSort(a: string) returns (b: string)
requires forall i :: 0 <= i < |a| ==> a[i] in {'a', 'b', 'd'}
ensures sortedbad(b)
ensures multiset(b[..]) == multiset(a[..])
{
  b := a;
  var next: int := 0;
  var aPointer: int := 0;
  var dPointer: int := |b|;

  while next != dPointer
    invariant 0 <= aPointer <= next <= dPointer <= |b|
    invariant multiset(b[..]) == multiset(a[..])
    invariant forall i :: 0 <= i < aPointer ==> b[i] == 'a'
    invariant forall i :: aPointer <= i < next ==> b[i] == 'b'
    invariant forall i :: dPointer <= i < |b| ==> b[i] == 'd'
    invariant forall i :: 0 <= i < |b| ==> b[i] in {'a', 'b', 'd'}
  {
    if b[next] == 'a' {
      b := b[next := b[aPointer]][aPointer := b[next]];
      next := next + 1;
      aPointer := aPointer + 1;
    } 
    else if b[next] == 'b' {
      next := next + 1;
    }
    else { // b[next] == 'd'
      dPointer := dPointer - 1;
      b := b[next := b[dPointer]][dPointer := b[next]];
    } 
  }
}