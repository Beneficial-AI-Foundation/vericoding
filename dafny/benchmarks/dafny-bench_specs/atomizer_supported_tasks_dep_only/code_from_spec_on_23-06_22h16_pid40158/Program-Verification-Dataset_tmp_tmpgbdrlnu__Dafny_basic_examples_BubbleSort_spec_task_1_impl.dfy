// ATOM 
predicate sorted(a:array<int>, from:int, to:int)
  requires a != null;
  reads a;
  requires 0 <= from <= to <= a.Length;
{
  forall u, v :: from <= u < v < to ==> a[u] <= a[v]
}

//IMPL bubbleSort
method bubbleSort (a: array<int>)
  requires a != null && a.Length > 0;
  modifies a;
  ensures sorted(a, 0, a.Length);
  ensures multiset(a[..]) == multiset(old(a[..]));
{
  var n := a.Length;
  var i := 0;
  
  while i < n - 1
    invariant 0 <= i <= n - 1;
    invariant multiset(a[..]) == multiset(old(a[..]));
    /* code modified by LLM (iteration 1): Fixed outer loop invariant to correctly state that the last i elements are sorted and in their final positions */
    invariant sorted(a, n - i, n);
    invariant forall u, v :: 0 <= u < n - i <= v < n ==> a[u] <= a[v];
  {
    var j := 0;
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i;
      invariant multiset(a[..]) == multiset(old(a[..]));
      /* code modified by LLM (iteration 1): Updated invariants to reflect that the last i elements remain sorted and the maximum element in the unsorted portion is being bubbled */
      invariant sorted(a, n - i, n);
      invariant forall u, v :: 0 <= u < n - i <= v < n ==> a[u] <= a[v];
      invariant forall k :: 0 <= k < j ==> a[k] <= a[j];
    {
      if a[j] > a[j + 1] {
        var temp := a[j];
        a[j] := a[j + 1];
        a[j + 1] := temp;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}