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
proof fn lemma_sum_to_loop_invariant(a: &Vec<i32>, i: int)
    requires
        0 <= i,
        i <= a.len(),
    ensures
        forall |k: int| 0 <= k <= i ==> sum_to(a, k) == sum_to(a, k),
{
}

/* helper modified by LLM (iteration 5): fixed type mismatch by using usize index for array access */
proof fn lemma_sum_to_step(a: &Vec<i32>, current_sum: i32, i: usize)
    requires
        0 <= i,
        i < a.len(),
        current_sum == sum_to(a, i as int),
    ensures
        current_sum + a[i] == sum_to(a, i as int + 1),
{
    assert(sum_to(a, i as int + 1) == sum_to(a, i as int) + a[i as int]);
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
    /* code modified by LLM (iteration 5): fixed type mismatch by using usize index for array access */
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            sum == sum_to(a, i as int),
        decreases a.len() - i
    {
        proof {
            lemma_sum_to_step(a, sum, i);
        }
        sum = sum + a[i];
        i = i + 1;
    }
    
    sum
}
// </vc-code>

}
fn main() {}