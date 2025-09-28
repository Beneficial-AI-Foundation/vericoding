// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 3): Added decreases clause to fix verification error */
    let mut result: Vec<i8> = Vec::new();
    let mut current = start;
    let mut count: usize = 0;
    
    while count < n
        invariant
            result@.len() == count,
            current == start as int + count as int * step as int,
            count <= n,
            forall|i: int| 0 <= i < result@.len() ==> result@[i] == start as int + i * step as int,
            forall|i: int| 0 <= i < result@.len() ==> result@[i] < stop as int,
        decreases n - count
    {
        result.push(current);
        current = current + step;
        count = count + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}