// ATOM 
predicate sorted(a: array?<int>, l: int, u: int)
  reads a;
  requires a != null;
  {
    forall i, j :: 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
  }

// ATOM 
predicate partitioned(a: array?<int>, i: int)
  reads a
  requires a != null
  {
    forall k, k' :: 0 <= k <= i < k' < a.Length ==> a[k] <= a[k']
  }

// IMPL BubbleSort
method BubbleSort(a: array?<int>)
  modifies a
  requires a != null
  ensures sorted(a, 0, a.Length - 1)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var n := a.Length;
  /* code modified by LLM (iteration 1): Added guard for empty array */
  if n <= 1 {
    return;
  }
  
  var i := 0;
  
  /* code modified by LLM (iteration 1): Fixed outer loop with proper bubble sort invariants */
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant sorted(a, n - i, n - 1)
    invariant forall k, k' :: 0 <= k < n - i && n - i <= k' < n ==> a[k] <= a[k']
  {
    var j := 0;
    /* code modified by LLM (iteration 1): Fixed inner loop with bubble-up invariant */
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant sorted(a, n - i, n - 1)
      invariant forall k, k' :: 0 <= k < n - i && n - i <= k' < n ==> a[k] <= a[k']
      invariant forall k :: 0 <= k < j ==> a[k] <= a[j]
    {
      if a[j] > a[j + 1] {
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

// IMPL Main  
method Main() {
}