predicate sorted_seg(a:array<int>, i:int, j:int) //j excluded
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
lemma multiset_swap_lemma(s: seq<int>, i: int, j: int)
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
  var swapped := s[i := s[j]][j := s[i]];
  
  if i != j {
    assert swapped[i] == s[j] && swapped[j] == s[i];
    assert forall k :: 0 <= k < |s| && k != i && k != j ==> swapped[k] == s[k];
  }
}

predicate partitioned(a: array<int>, c: int, i: int, f: int)
  requires 0 <= c <= i < f <= a.Length
  reads a
{
  forall k, l :: c <= k <= i && i < l < f ==> a[k] <= a[l]
}
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
  if c >= f { return; }
  
  var i := f - 1;
  while i > c
    invariant c <= i < f
    invariant sorted_seg(a, i, f)
    invariant i < f - 1 ==> partitioned(a, c, i, f)
    invariant multiset(a[c..f]) == old(multiset(a[c..f]))
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
  {
    var j := c;
    while j < i
      invariant c <= j <= i
      invariant sorted_seg(a, i, f)
      invariant i < f - 1 ==> partitioned(a, c, i, f)
      invariant forall k :: c <= k <= j ==> a[k] <= a[j]
      invariant multiset(a[c..f]) == old(multiset(a[c..f]))
      invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    {
      if a[j] > a[j+1] {
        var old_seq := a[c..f];
        var temp := a[j];
        a[j] := a[j+1];
        a[j+1] := temp;
        
        // Apply the lemma to prove multiset preservation
        var local_old := old_seq;
        var local_new := a[c..f];
        multiset_swap_lemma(local_old, j-c, j+1-c);
        
        assert multiset(a[c..f]) == multiset(old_seq);
      }
      j := j + 1;
    }
    i := i - 1;
  }
}
// </vc-code>