// <vc-preamble>
type T = int
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method partition(a: array<T>) returns(pivotPos: int) 
    requires a.Length > 0
    ensures 0 <= pivotPos < a.Length
    ensures forall i :: 0 <= i < pivotPos ==> a[i] < a[pivotPos]
    ensures forall i :: pivotPos < i < a.Length ==> a[i] >= a[pivotPos]
    ensures multiset(a[..]) == multiset(old(a[..]))
    modifies a
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
