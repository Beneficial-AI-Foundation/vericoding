// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no helpers needed */
// </vc-helpers>

// <vc-spec>
method ChooseOdd(v: array<int>) returns (odd_index: int)
    requires exists q :: 0 <= q < v.Length && v[q] % 2 == 1
    ensures 0 <= odd_index < v.Length
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fix postcondition by ensuring the loop finds an odd element */
{
  odd_index := 0;
  while odd_index < v.Length
    invariant 0 <= odd_index <= v.Length
    invariant forall k :: 0 <= k < odd_index ==> v[k] % 2 != 1
    decreases v.Length - odd_index
  {
    if v[odd_index] % 2 == 1 {
      return;
    }
    odd_index := odd_index + 1;
  }
  // The loop must find an odd element and return because of the `requires` clause.
  // If the loop finished without returning, it would contradict the `requires` clause.
  // Dafny infers that `odd_index` must satisfy the postconditions due to the invariant and the `requires` clause.
}
// </vc-code>
