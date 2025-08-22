//IMPL 
method BubbleSort(a: array<int>)
  modifies a
  ensures forall i,j::0<= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..])==multiset(old(a[..]))
{
  var n := a.Length;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    /* code modified by LLM (iteration 4): Fixed sortedness invariant - last i elements are sorted */
    invariant forall p, q :: n - i <= p < q < n ==> a[p] <= a[q]
    invariant multiset(a[..]) == multiset(old(a[..]))
    /* code modified by LLM (iteration 4): Fixed partition invariant - sorted suffix elements are >= unsorted prefix elements */
    invariant forall p, q :: 0 <= p < n - i && n - i <= q < n ==> a[p] <= a[q]
  {
    if i < n - 1 {
      var j := 0;
      
      while j < n - i - 1
        invariant 0 <= j <= n - i - 1
        /* code modified by LLM (iteration 4): Maintained outer loop invariants in inner loop */
        invariant forall p, q :: n - i <= p < q < n ==> a[p] <= a[q]
        invariant multiset(a[..]) == multiset(old(a[..]))
        invariant forall p, q :: 0 <= p < n - i && n - i <= q < n ==> a[p] <= a[q]
        /* code modified by LLM (iteration 4): Corrected bubble invariant - maximum of processed elements is at position j */
        invariant forall k :: 0 <= k <= j ==> a[k] <= a[j]
      {
        if a[j] > a[j + 1] {
          var temp := a[j];
          a[j] := a[j + 1];
          a[j + 1] := temp;
        }
        j := j + 1;
      }
    }
    i := i + 1;
  }
}