predicate sorted_seg(a:array<int>, i:int, j:int) //j excluded
requires 0 <= i <= j <= a.Length
reads a
{
  forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

//IMPL
method bubbleSort(a:array<int>, c:int, f:int)//f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
{
  if c >= f {
    return;
  }
  
  var i := c;
  while i < f - 1
    invariant c <= i <= f
    invariant sorted_seg(a, c, i + 1)
    /* code modified by LLM (iteration 4): Removed problematic separation invariant - will be established by inner loop */
    invariant multiset(a[c..f]) == old(multiset(a[c..f]))
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
  {
    var j := f - 1;
    while j > i
      /* code modified by LLM (iteration 4): Fixed bounds - j decreases from f-1 down to i+1 */
      invariant i < j <= f - 1
      /* code modified by LLM (iteration 4): Track that a[j] is minimum in remaining unsorted part */
      invariant forall k :: j < k < f ==> a[j] <= a[k]
      /* code modified by LLM (iteration 4): Maintain sorted property of processed segment */
      invariant sorted_seg(a, c, i + 1)
      invariant multiset(a[c..f]) == old(multiset(a[c..f]))
      invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    {
      if a[j - 1] > a[j] {
        a[j - 1], a[j] := a[j], a[j - 1];
      }
      j := j - 1;
    }
    /* code modified by LLM (iteration 4): After inner loop, establish that a[i+1] fits properly between sorted and unsorted parts */
    assert j == i + 1;
    assert forall k :: i + 1 < k < f ==> a[i + 1] <= a[k];
    assert sorted_seg(a, c, i + 1);
    i := i + 1;
    /* code modified by LLM (iteration 4): After incrementing i, we now have sorted_seg(a, c, i + 1) which is sorted_seg(a, c, (i-1) + 2) */
  }
}