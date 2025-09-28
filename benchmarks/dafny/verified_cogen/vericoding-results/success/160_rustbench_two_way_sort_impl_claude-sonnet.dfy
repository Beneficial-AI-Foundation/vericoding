// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsSorted(a: array<bool>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> !a[i] || a[j]
}
// </vc-helpers>

// <vc-spec>
method TwoWaySort(a: array<bool>)
    requires a.Length <= 100_000
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures forall i, j :: 0 <= i < j < a.Length ==> !a[i] || a[j]
    modifies a
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): removed unused helper lemma and old_a reference */
    var left := 0;
    var right := a.Length;
    
    while left < right
        invariant 0 <= left <= right <= a.Length
        invariant multiset(a[..]) == old(multiset(a[..]))
        invariant forall i :: 0 <= i < left ==> !a[i]
        invariant forall i :: right <= i < a.Length ==> a[i]
    {
        if !a[left] {
            left := left + 1;
        } else {
            right := right - 1;
            a[left], a[right] := a[right], a[left];
        }
    }
}
// </vc-code>
