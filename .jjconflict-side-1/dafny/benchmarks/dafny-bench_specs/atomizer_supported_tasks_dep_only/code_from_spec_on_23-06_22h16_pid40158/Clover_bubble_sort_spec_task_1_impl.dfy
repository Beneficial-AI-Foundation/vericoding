//IMPL BubbleSort
method BubbleSort(a: array<int>)
  modifies a
  ensures forall i,j::0<= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..])==multiset(old(a[..]))
{
  var n := a.Length;
  var i := 0;
  
  while i < n
    /* code modified by LLM (iteration 1): Fixed outer loop invariants to correctly track that elements from position n-i onwards are sorted and in their final positions */
    invariant 0 <= i <= n
    invariant forall p, q :: n - i <= p < q < n ==> a[p] <= a[q]
    invariant forall p, q :: 0 <= p < n - i && n - i <= q < n ==> a[p] <= a[q]
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var j := 0;
    while j < n - 1 - i
      /* code modified by LLM (iteration 1): Fixed inner loop invariants to track the bubbling process and maintain outer loop properties */
      invariant 0 <= j <= n - 1 - i
      invariant forall p, q :: n - i <= p < q < n ==> a[p] <= a[q]
      invariant forall p, q :: 0 <= p < n - i && n - i <= q < n ==> a[p] <= a[q]
      invariant forall k :: 0 <= k <= j ==> a[k] <= a[j]
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      if a[j] > a[j + 1] {
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}