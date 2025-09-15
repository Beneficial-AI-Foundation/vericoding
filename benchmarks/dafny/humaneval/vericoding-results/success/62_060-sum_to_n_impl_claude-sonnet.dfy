// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added lemma to prove loop invariant about sum formula */
lemma SumFormula(k: int)
  requires k >= 0
  ensures k * (k + 1) / 2 == (if k == 0 then 0 else (k - 1) * k / 2 + k)
{
  if k == 0 {
    // Base case: 0 * 1 / 2 == 0
  } else {
    // Inductive case: k * (k + 1) / 2 == (k - 1) * k / 2 + k
    // This follows from algebraic manipulation
  }
}
// </vc-helpers>

// <vc-spec>
method sum_to_n(n: int) returns (r : int)

  ensures r == n * (n + 1) / 2
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Simplified implementation with direct formula calculation */
  r := n * (n + 1) / 2;
}
// </vc-code>
