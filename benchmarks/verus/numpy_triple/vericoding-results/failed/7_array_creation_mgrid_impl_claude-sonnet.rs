// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed parameter types and scope issues */
proof fn lemma_arithmetic_bounds(start: i8, stop: i8, step: i8, i: usize, n: usize)
    requires
        step > 0,
        i < n,
        n == ((stop as int - start as int) / step as int) as usize,
        start < stop,
    ensures
        start as int + (i as int) * (step as int) <= i8::MAX as int,
        start as int + (i as int) * (step as int) >= i8::MIN as int,
{
}

proof fn lemma_step_bounds(start: i8, step: i8, stop: i8, i: usize, n: usize)
    requires
        step > 0,
        start < stop,
        i < n,
        n == ((stop as int - start as int) / step as int) as usize,
    ensures
        start as int + (i as int) * (step as int) < stop as int,
{
}
// </vc-helpers>

// <vc-spec>
fn mgrid(start: i8, stop: i8, step: i8, n: usize) -> (result: Vec<i8>)
    requires
        step > 0,
        start < stop,
        n == ((stop as int - start as int) / step as int) as usize,
    ensures
        result@.len() == n,
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] == start as int + i * step as int,
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] < stop as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): moved int calculations to ghost blocks */
    let mut result: Vec<i8> = Vec::new();
    let mut i = 0;
    
    while i < n
        invariant
            result@.len() == i,
            i <= n,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == start as int + j * step as int,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] < stop as int,
        decreases n - i
    {
        let ghost current_val: int = start as int + (i as int) * (step as int);
        proof {
            lemma_step_bounds(start, step, stop, i, n);
            lemma_arithmetic_bounds(start, stop, step, i, n);
        }
        
        let current = start + (i as i8) * step;
        result.push(current);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}