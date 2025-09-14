predicate sorted_seg(a:array<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= a.Length
reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

// <vc-helpers>
lemma SortedSegExtend(a: array<int>, i: int, j: int, k: int)
  requires 0 <= i <= j < k < a.Length
  requires sorted_seg(a, i, j)
  requires forall l :: i <= l <= j ==> a[l] <= a[k]
  ensures sorted_seg(a, i, k)
{
  assert forall l, m :: i <= l <= m <= k ==> 
    if m <= j then a[l] <= a[m]
    else if l <= j then a[l] <= a[k] 
    else a[l] <= a[m];
}

lemma SortedSegPreserved(a: array<int>, i: int, j: int, pos: int, val: int)
  requires 0 <= i <= j < a.Length
  requires 0 <= pos < a.Length
  requires pos < i || pos > j
  requires sorted_seg(a, i, j)
  ensures sorted_seg(a, i, j)
{
}

lemma MultisetShift(a: array<int>, i: int)
  requires 0 <= i < a.Length - 1
  ensures multiset(a[..]) == old(multiset(a[..])) + multiset{a[i+1]} - multiset{old(a[i+1])} + multiset{a[i]} - multiset{old(a[i])}
{
}

lemma SortedSegCombine(a: array<int>, i: int, j: int, k: int)
  requires 0 <= i <= j+1 <= k+1 <= a.Length
  requires sorted_seg(a, i, j)
  requires sorted_seg(a, j+1, k)
  requires j >= i-1 && j+1 < a.Length ==> forall l :: i <= l <= j ==> a[l] <= a[j+1]
  ensures sorted_seg(a, i, k)
{
  if i <= j && j+1 <= k {
    assert forall l, m :: i <= l <= m <= k ==>
      if m <= j then a[l] <= a[m]
      else if l <= j then a[l] <= a[j+1] && a[j+1] <= a[m]
      else a[l] <= a[m];
  }
}

lemma SortedSegEmpty(a: array<int>, i: int)
  requires 0 <= i < a.Length
  ensures sorted_seg(a, i, i-1)
{
}

lemma SortedSegSingle(a: array<int>, i: int)
  requires 0 <= i < a.Length
  ensures sorted_seg(a, i, i)
{
}
// </vc-helpers>

// <vc-spec>
method InsertionSort(a: array<int>)
  modifies a;
  ensures sorted_seg(a,0,a.Length-1) 
  ensures multiset(a[..]) == old(multiset(a[..])) //Add and prove this
// </vc-spec>
// <vc-code>
{
  if a.Length <= 1 {
    return;
  }
  
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant sorted_seg(a, 0, i-1)
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var key := a[i];
    var j := i - 1;
    ghost var oldArray := a[..];
    
    while j >= 0 && a[j] > key
      invariant -1 <= j < i
      invariant sorted_seg(a, 0, j)
      invariant j+1 < i ==> a[j+1] == key
      invariant j+2 <= i ==> sorted_seg(a, j+2, i)
      invariant forall l :: j+2 <= l <= i ==> a[l] >= key
      invariant multiset(a[..]) == multiset(oldArray)
      invariant a[j+1..i+1] == [key] + oldArray[j+1..i]
    {
      a[j+1] := a[j];
      j := j - 1;
    }
    
    a[j+1] := key;
    
    assert sorted_seg(a, 0, j);
    assert j+1 < a.Length && a[j+1] == key;
    assert j+2 <= i ==> sorted_seg(a, j+2, i);
    assert forall l :: 0 <= l <= j ==> a[l] <= key;
    assert forall l :: j+2 <= l <= i ==> a[l] >= key;
    assert sorted_seg(a, 0, i);
    
    i := i + 1;
  }
}
// </vc-code>

