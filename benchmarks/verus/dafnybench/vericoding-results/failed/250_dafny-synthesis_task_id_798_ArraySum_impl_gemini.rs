// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_to(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_sum(a: &[i32]) -> (result: i32)
    ensures result == sum_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): used correct slice indexing `a@[i as int]` in proof block */
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum as int == sum_to(a, i as int),
            ensures (sum as int == sum_to(a, a.len() as int)),
            forall|j: int| i as int <= j <= a.len() as int ==> i32::MIN <= sum_to(a, j) - sum_to(a, i as int) <= i32::MAX,
        decreases a.len() - i
    {
        proof {
            assert(sum_to(a, (i + 1) as int) == sum_to(a, i as int) + a@[i as int] as int) by {
                reveal(sum_to);
            };
            let next_sum_to = sum_to(a, (i + 1) as int);
            let next_sum_val = sum as int + a@[i as int] as int;
            assert(next_sum_val == next_sum_to);
        }
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}
// </vc-code>

}
fn main() {}