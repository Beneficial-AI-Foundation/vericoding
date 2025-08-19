//ATOM
predicate sorted_seg(a:array<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= a.Length
reads a
{
  forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

//IMPL 
method InsertionSort(a: array<int>)
 modifies a
 ensures sorted_seg(a,0,a.Length-1) 
 ensures multiset(a[..]) == old(multiset(a[..])) //Add and prove this
{
  if a.Length <= 1 { return; }
  
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant sorted_seg(a, 0, i-1)
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    /* code modified by LLM (iteration 3): Store original array state for multiset reasoning */
    ghost var a_before_inner := a[..];
    var key := a[i];
    var j := i - 1;
    
    while j >= 0 && a[j] > key
      invariant -1 <= j <= i - 1
      invariant sorted_seg(a, 0, j)
      invariant sorted_seg(a, j+2, i)
      invariant forall k :: j+2 <= k <= i ==> key <= a[k]
      invariant multiset(a[..]) == multiset(a_before_inner)
      invariant forall k :: 0 <= k <= j ==> a[k] == a_before_inner[k]
      invariant forall k :: j+2 <= k <= i ==> a[k] == a_before_inner[k-1]
      invariant a[j+1] == a_before_inner[j+1] || (j < i-1 && a[j+1] != key)
      /* code modified by LLM (iteration 3): Added element preservation invariant */
    {
      a[j+1] := a[j];
      j := j - 1;
    }
    
    a[j+1] := key;
    /* code modified by LLM (iteration 3): Assert multiset preservation after key insertion */
    assert multiset(a[..]) == multiset(a_before_inner);
    i := i + 1;
  }
}