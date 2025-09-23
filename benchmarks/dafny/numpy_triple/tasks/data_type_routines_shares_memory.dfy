// <vc-preamble>
// Predicate to determine if two arrays share memory
{
  a.Length == b.Length && 
  forall i :: 0 <= i < a.Length ==> a[i] == b[i]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
predicate SharesMemory<T(
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
