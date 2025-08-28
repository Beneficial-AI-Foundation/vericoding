predicate sorted_seg(a:array<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= a.Length
reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

// <vc-helpers>
lemma InsertPreservesMultiset(a: array<int>, i: int)
  requires 0 <= i < a.Length
  ensures multiset(a[..i] + [a[i]] + a[i+1..]) == multiset(a[..])
{
  calc {
    multiset(a[..i] + [a[i]] + a[i+1..]);
    == multiset(a[..i]) + multiset([a[i]]) + multiset(a[i+1..]);
    == multiset(a[..i]) + multiset(a[i+1..]) + multiset([a[i]]);
    == multiset(a[..i] + a[i+1..]) + multiset([a[i]]);
    == multiset(a[..]);
  }
}

lemma MultisetPreservation(a: array<int>, i: int, j: int, val: int)
  requires 0 <= i <= j+1 <= a.Length
  ensures multiset(a[..i] + a[i..j+1] + [val] + a[j+1..]) == multiset(a[..i] + [val] + a[i..j+1] + a[j+1..])
{
  calc {
    multiset(a[..i] + a[i..j+1] + [val] + a[j+1..]);
    == multiset(a[..i]) + multiset(a[i..j+1]) + multiset([val]) + multiset(a[j+1..]);
    == multiset(a[..i]) + multiset([val]) + multiset(a[i..j+1]) + multiset(a[j+1..]);
    == multiset(a[..i] + [val] + a[i..j+1] + a[j+1..]);
  }
}

lemma ShiftPreservesMultiset(a: array<int>, i: int, j: int)
  requires 0 <= i <= j < a.Length
  ensures multiset(a[..i] + a[i+1..j+1] + [a[i]] + a[j+1..]) == multiset(a[..])
{
  calc {
    multiset(a[..i] + a[i+1..j+1] + [a[i]] + a[j+1..]);
    == multiset(a[..i]) + multiset(a[i+1..j+1]) + multiset([a[i]]) + multiset(a[j+1..]);
    == multiset(a[..i]) + multiset(a[i+1..j+1]) + multiset(a[j+1..]) + multiset([a[i]]);
    == multiset(a[..i] + [a[i]] + a[i+1..j+1] + a[j+1..]);
    == multiset(a[..]);
  }
}

lemma SortedSegExtension(a: array<int>, i: int, j: int, key: int)
  requires 0 <= i <= j+1 <= a.Length
  requires sorted_seg(a, i, j)
  requires j+1 < a.Length ==> a[j] <= key
  ensures sorted_seg(a, i, j+1)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method InsertionSort(a: array<int>)
  modifies a;
  ensures sorted_seg(a,0,a.Length-1) 
  ensures multiset(a[..]) == old(multiset(a[..])) //Add and prove this
// </vc-spec>
// </vc-spec>

// <vc-code>
method InsertionSortImpl(a: array<int>)
  modifies a
  ensures sorted_seg(a, 0, a.Length-1)
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  if a.Length <= 1 {
    return;
  }
  
  var i := 1;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant sorted_seg(a, 0, i-1)
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var key := a[i];
    var j := i - 1;
    
    while j >= 0 && a[j] > key
      invariant -1 <= j < i <= a.Length
      invariant multiset(a[..]) == old(multiset(a[..]))
      invariant sorted_seg(a, 0, j)
      invariant forall k :: j+1 <= k <= i ==> a[k] >= key
    {
      a[j+1] := a[j];
      j := j - 1;
    }
    
    a[j+1] := key;
    if j >= 0 {
      MultisetPreservation(a, 0, j, key);
    }
    i := i + 1;
  }
}
// </vc-code>
