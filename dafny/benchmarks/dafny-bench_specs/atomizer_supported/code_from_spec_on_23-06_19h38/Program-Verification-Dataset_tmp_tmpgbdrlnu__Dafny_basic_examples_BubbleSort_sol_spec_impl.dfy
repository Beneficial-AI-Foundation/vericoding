// ATOM 
predicate sorted_between (a:array<int>, from:nat, to:nat)
  reads a;
  requires a != null;
  requires from <= to;
  requires to <= a.Length;
{
  forall i,j :: from <= i < j < to && 0 <= i < j < a.Length ==> a[i] <= a[j]
}

  
// ATOM 
  
predicate sorted (a:array<int>)
  reads a;
  requires a!=null;
{
  sorted_between (a, 0, a.Length)
}


// IMPL bubbleSort

method bubbleSort (a: array<int>)
  modifies a;
  requires a != null;
  requires a.Length > 0;
  ensures sorted(a);
  ensures multiset(old(a[..])) == multiset(a[..]);
{
  var n := a.Length;
  var i := 0;
  
  while i < n - 1
    invariant 0 <= i <= n - 1;
    invariant multiset(old(a[..])) == multiset(a[..]);
    /* code modified by LLM (iteration 1): Fixed invariant to correctly express that elements from n-i to n are in their final sorted positions and are greater than or equal to elements before them */
    invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> a[k] <= a[l];
    /* code modified by LLM (iteration 1): Fixed invariant to express that the last i elements are sorted among themselves */
    invariant sorted_between(a, n - i, n);
  {
    var j := 0;
    
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i;
      invariant multiset(old(a[..])) == multiset(a[..]);
      invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> a[k] <= a[l];
      invariant sorted_between(a, n - i, n);
      /* code modified by LLM (iteration 1): Added invariant to ensure the maximum element in the unsorted portion is bubbled to position j */
      invariant forall k :: 0 <= k <= j ==> a[k] <= a[j];
    {
      if a[j] > a[j + 1] {
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}