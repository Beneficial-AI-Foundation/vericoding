// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed type conversions that cause compilation errors in non-ghost code */
proof fn helper_lemma_mgrid_properties(start: i8, stop: i8, step: i8, n: usize, i: int)
    requires
        step > 0,
        start < stop,
        n == ((stop as int - start as int) / step as int) as usize,
        0 <= i < n as int,
    ensures
        (start as int) + i * (step as int) < stop as int,
{
    let total_range = stop as int - start as int;
    let step_int = step as int;
    assert(n as int * step_int <= total_range);
    assert(i < n as int);
    assert(i * step_int < n as int * step_int);
    assert((start as int) + i * step_int < (start as int) + total_range);
    assert((start as int) + total_range == stop as int);
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
/* code modified by LLM (iteration 5): Removed int conversions to fix compilation errors */
{
    let mut result = Vec::new();
    let mut current: i8 = start;
    let mut count: usize = 0;
    
    while current < stop
        invariant
            count <= n,
            result@.len() == count,
            forall|j: int| 0 <= j < count ==> #[trigger] result@[j] == (start as int) + j * (step as int),
            current as int == (start as int) + count as int * (step as int),
        decreases n - count,
    {
        proof {
            helper_lemma_mgrid_properties(start, stop, step, n, count as int);
        }
        result.push(current);
        current = (current as i32 + step as i32) as i8;
        count = count + 1;
    }
    
    assert(count == n);
    result
}
// </vc-code>


}
fn main() {}