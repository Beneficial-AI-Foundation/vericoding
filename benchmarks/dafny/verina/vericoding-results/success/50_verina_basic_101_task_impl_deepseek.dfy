// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

lemma triple_factor(x: int) 
  ensures (x * 3) / 3 == x 
{
  /* proof follows from integer arithmetic properties */
}

// </vc-helpers>

// <vc-spec>
method triple(x: int) returns (result: int)
    ensures
        result / 3 == x &&
        result / 3 * 3 == result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Removed axiom bypass, added proper return value */
  result := x * 3;
}
// </vc-code>
