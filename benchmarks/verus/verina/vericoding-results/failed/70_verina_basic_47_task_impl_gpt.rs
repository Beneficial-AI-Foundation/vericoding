// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_to(a: &Vec<i32>, n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reveals to unfold sum_to at base and step cases */
proof fn lemma_sum_to_zero(a: &Vec<i32>)
    ensures sum_to(a, 0) == 0
{
    reveal(sum_to);
}

/* helper modified by LLM (iteration 2): establishes recursive step by revealing sum_to at n > 0 */
proof fn lemma_sum_to_step(a: &Vec<i32>, n: int)
    requires 0 < n <= a.len() as int
    ensures sum_to(a, n) == sum_to(a, n - 1) + a[n - 1]
{
    reveal(sum_to);
}
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        result == sum_to(a, a.len() as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implemented iterative sum with proper loop invariants and decreases */
    let len = a.len();
    let mut i: usize = 0;
    let mut acc: i32 = 0;
    proof { lemma_sum_to_zero(a); }
    while i < len
        invariant
            0 <= i as int <= len as int,
            acc == sum_to(a, i as int)
        decreases (len - i) as int
    {
        proof {
            // Satisfy preconditions for the step lemma
            assert(0 < i as int + 1);
            assert(i < len);
            assert(i as int + 1 <= len as int);
            lemma_sum_to_step(a, i as int + 1);
        }
        acc = acc + a[i];
        i = i + 1;
    }
    acc
}
// </vc-code>

}
fn main() {}