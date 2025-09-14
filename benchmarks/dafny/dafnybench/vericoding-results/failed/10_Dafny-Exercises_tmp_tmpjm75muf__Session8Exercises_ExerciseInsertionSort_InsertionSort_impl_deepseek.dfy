predicate sorted_seg(a:array<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= a.Length
reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

// <vc-helpers>
predicate sorted_seg(a:array<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= a.Length
reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

lemma SortedSegLemma(a: array<int>, i: int, j: int)
  requires 0 <= i <= j+1 <= a.Length
  requires sorted_seg(a, i, j)
  requires j+1 < a.Length
  requires a[j] <= a[j+1]
  ensures sorted_seg(a, i, j+1)
{
}

lemma MultisetLemma(a: array<int>, i: int, j: int)
  requires 0 <= i <= j < a.Length
  requires a.Length > 0
  ensures multiset(a[..]) == old(multiset(a[..]))
  ensures forall k :: i <= k <= j && k+1 < a.Length ==> a[k] == old(a[k+1]) && a[k+1] == old(a[k])
{
}

lemma SortedSegExtension(a: array<int>, i: int, j: int, key: int)
  requires 0 <= i <= j+1 <= a.Length
  requires sorted_seg(a, i, j)
  requires j < a.Length - 1
  requires forall k :: i <= k <= j ==> a[k] <= key
  ensures sorted_seg(a, i, j+1)
{
}

lemma SortedSegZero(a: array<int>)
  requires a.Length >= 0
  ensures sorted_seg(a, 0, -1)
{
}

lemma SortedSegTransitivity(a: array<int>, i: int, j: int, k: int)
  requires 0 <= i <= j <= k < a.Length
  requires sorted_seg(a, i, j)
  requires sorted_seg(a, j, k)
  requires j < k ==> a[j] <= a[j+1]
  ensures sorted_seg(a, i, k)
{
}

lemma SortedSegSingleton(a: array<int>, i: int)
  requires 0 <= i < a.Length
  ensures sorted_seg(a, i, i)
{
}

lemma SortedSegCombine(a: array<int>, i: int, j: int, k: int)
  requires 0 <= i <= j <= k < a.Length
  requires sorted_seg(a, i, j)
  requires sorted_seg(a, j, k)
  requires j < k ==> a[j] <= a[j+1]
  ensures sorted_seg(a, i, k)
{
}

lemma SortedSegUpdate(a: array<int>, i: int, j: int)
  requires 0 <= i <= j < a.Length
  requires sorted_seg(a, i, j)
  requires j+1 < a.Length
  requires a[j] <= a[j+1]
  ensures sorted_seg(a, i, j+1)
{
}

lemma SortedSegShift(a: array<int>, i: int, j: int, key: int)
  requires 0 <= i <= j < a.Length
  requires sorted_seg(a, i, j)
  requires forall k :: i <= k <= j ==> a[k] <= key
  ensures sorted_seg(a, i, j+1)
  ensures a[j+1] == key
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
    
    while j >= 0 && a[j] > key
      invariant -1 <= j < i
      invariant forall k :: j+1 <= k <= i ==> a[k] == old(a[k])
      invariant multiset(a[..]) == old(multiset(a[..]))
      invariant j >= 0 ==> forall k :: 0 <= k <= j ==> a[k] <= key
      invariant sorted_seg(a, 0, j)
      invariant j >= 0 ==> sorted_seg(a, j+1, i)
    {
      a[j+1] := a[j];
      j := j - 1;
    }
    
    a[j+1] := key;
    
    if j >= 0 {
      SortedSegCombine(a, 0, j, i);
    } else {
      SortedSegSingleton(a, 0);
      if i > 0 {
        SortedSegTransitivity(a, 0, 0, i);
      }
    }
    i := i + 1;
  }
}
// </vc-code>

