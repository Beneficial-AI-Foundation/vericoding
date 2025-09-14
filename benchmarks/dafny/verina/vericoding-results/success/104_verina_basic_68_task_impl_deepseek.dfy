// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsPresent(a: array<int>, e: int, lo: nat, hi: nat) 
  reads a
  requires lo <= hi
  requires hi <= a.Length
  ensures IsPresent(a, e, lo, hi) == (exists i :: lo <= i < hi && a[i] == e)
  decreases hi - lo
{
  if lo >= hi then false else (a[lo] == e || IsPresent(a, e, lo + 1, hi))
}
// </vc-helpers>

// <vc-spec>
method LinearSearch(a: array<int>, e: int) returns (result: nat)
    ensures result <= a.Length
    ensures result == a.Length || a[result] == e
    ensures forall i :: 0 <= i < result ==> a[i] != e
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed array bounds and verification */
  result := 0;
  while result < a.Length
    invariant result <= a.Length
    invariant forall i :: 0 <= i < result ==> a[i] != e
    decreases a.Length - result
  {
    if a[result] == e {
      return;
    }
    result := result + 1;
  }
}
// </vc-code>
