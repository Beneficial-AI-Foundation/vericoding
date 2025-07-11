//ATOM FindMin
//b)
//Problem04
method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
  requires a != null && a.Length > 0 && lo < a.Length
  ensures lo <= minIdx < a.Length
  ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
  minIdx := lo;
  var k := lo + 1;
  while k < a.Length
    invariant lo <= minIdx < a.Length
    invariant lo <= k <= a.Length
    invariant forall x :: lo <= x < k ==> a[minIdx] <= a[x]
  {
    if a[k] < a[minIdx] {
      minIdx := k;
    }
    k := k + 1;
  }
}


//ATOM swap
//Problem01
//a)
method swap(a: array<int>, i: nat, j: nat)
  modifies a
  requires a != null && a.Length > 0 && i < a.Length && j < a.Length
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}


//IMPL selectionSort

/* code modified by LLM (iteration 1): added helper predicate for sorted property */
predicate sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method selectionSort(a: array<int>)
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures sorted(a[..])
{
  /* code modified by LLM (iteration 1): removed null check (arrays are non-nullable) and added proper edge case handling */
  if a.Length <= 1 {
    return;
  }
  
  var i := 0;
  /* code modified by LLM (iteration 1): updated loop invariants to properly verify multiset preservation and sorting properties */
  while i < a.Length - 1
    invariant 0 <= i <= a.Length - 1
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall x, y :: 0 <= x < y < i ==> a[x] <= a[y]
    invariant forall x, y :: 0 <= x < i <= y < a.Length ==> a[x] <= a[y]
  {
    var minIdx := FindMin(a, i);
    if minIdx != i {
      swap(a, i, minIdx);
    }
    i := i + 1;
  }
}