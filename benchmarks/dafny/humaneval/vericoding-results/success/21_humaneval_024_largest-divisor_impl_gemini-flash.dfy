// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added precondition for k != 0. */
predicate is_divisor(n: int, k: int) requires k != 0 { n % k == 0 }
// </vc-helpers>

// <vc-spec>
method largest_divisor(n: int) returns (d : int)

  requires n > 1

  ensures 1 <= d < n
  ensures n % d == 0
  ensures forall k :: d < k < n ==> n % k != 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixes the largest_divisor method by ensuring the loop invariant and postconditions are met. */
{
    d := n - 1;
    while d > 1
        invariant 1 <= d < n
        invariant forall k :: d < k < n ==> n % k != 0
    {
        if is_divisor(n, d) {
            return;
        }
        d := d - 1;
    }
    d := 1;
    return;
}
// </vc-code>
