// <vc-preamble>
predicate sorted_seg(a:array<int>, i:int, j:int)
requires 0 <= i <= j+1 <= a.Length
reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method InsertionSort(a: array<int>)
  modifies a;
  ensures sorted_seg(a,0,a.Length-1) 
  ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed outer loop start and corrected inner loop invariant */
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant sorted_seg(a, 0, i - 1)
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    ghost var a_pre := a[..];
    var key := a[i];
    var j := i - 1;

    while j >= 0 && a[j] > key
      invariant -1 <= j < i
      invariant sorted_seg(a, 0, j)
      invariant forall k :: j+2 <= k <= i ==> a[k] > key
      invariant a[j+1] == key
      invariant multiset(a[..]) == multiset(a_pre)
      invariant forall k :: i < k < a.Length ==> a[k] == a_pre[k]
    {
      var tmp := a[j];
      a[j] := a[j+1];
      a[j+1] := tmp;
      j := j - 1;
    }
    i := i + 1;
  }
}
// </vc-code>
