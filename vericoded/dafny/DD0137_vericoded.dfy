predicate sorted_seg(a:array<int>, i:int, j:int) //j excluded
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
// No helpers required for this proof.
// </vc-helpers>

// <vc-spec>
method bubbleSorta(a:array<int>, c:int, f:int)//f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
// </vc-spec>
// <vc-code>
{
  var hi := f;
  ghost var orig := multiset(a[c..f]);
  while hi > c + 1
    invariant c <= hi <= f
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    invariant multiset(a[c..f]) == orig
    invariant sorted_seg(a, hi, f)
    invariant forall x :: hi <= x < f ==> forall y :: c <= y < hi ==> a[y] <= a[x]
    decreases hi - c
  {
    var j := c;
    while j + 1 < hi
      invariant c <= j < hi
      invariant forall p :: c <= p < j ==> a[p] <= a[j]
      invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
      invariant multiset(a[c..f]) == orig
      invariant sorted_seg(a, hi, f)
      invariant forall x :: hi <= x < f ==> forall y :: c <= y < hi ==> a[y] <= a[x]
      decreases hi - j
    {
      if a[j] > a[j+1] {
        var t := a[j];
        a[j] := a[j+1];
        a[j+1] := t;
      }
      j := j + 1;
    }
    hi := hi - 1;
  }
}
// </vc-code>

