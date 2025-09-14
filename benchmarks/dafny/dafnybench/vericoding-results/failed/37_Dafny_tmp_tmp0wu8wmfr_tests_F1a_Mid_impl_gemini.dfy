// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Mid( p: int, q: int) returns ( m: int )

    requires p <= q;
    ensures p<= m <= q;
    ensures m-p <= q-m;
    ensures 0 <= (q-m)-(m-p) <= 1;
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): The previous implementation was logically correct but the verifier failed due to unrelated compilation warnings. This version uses an alternative but equivalent formula p + (q-p)/2 to calculate the midpoint. */
  m := p + (q - p) / 2;
}
// </vc-code>
