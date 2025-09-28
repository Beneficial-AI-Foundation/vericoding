// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// Helper function to check if we can fit n elements in the range
spec fn can_fit_n_elements(start: i8, stop: i8, step: i8, n: usize) -> bool {
    if step > 0 {
        n == 0 || (start < stop && start as int + (n as int - 1) * step as int < stop as int)
    } else {
        n == 0 || (start > stop && start as int + (n as int - 1) * step as int > stop as int)
    }
}

/* helper modified by LLM (iteration 5): fixed syntax error by removing comma after condition */
proof fn lemma_bounds_maintained(start: i8, stop: i8, step: i8, n: usize, i: int)
    requires
        step != 0,
        0 <= i < n,
        can_fit_n_elements(start, stop, step, n)
    ensures
        step > 0 ==> start as int + i * step as int < stop as int,
        step < 0 ==> start as int + i * step as int > stop as int
{
    if step > 0 && n > 0 {
        assert(i <= n as int - 1);
        assert(start as int + i * step as int <= start as int + (n as int - 1) * step as int);
    } else if step < 0 && n > 0 {
        assert(i <= n as int - 1);
        assert(start as int + i * step as int >= start as int + (n as int - 1) * step as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn arange(start: i8, stop: i8, step: i8, n: usize) -> (result: Vec<i8>)
    requires step != 0,
    ensures
        result.len() == n,
        n == 0 ==> ((step > 0 && start >= stop) || (step < 0 && start <= stop)),
        n > 0 ==> (
            forall|i: int| 0 <= i < n ==> result@[i] == start as int + i * step as int
        ),
        n > 0 && step > 0 ==> (
            start < stop &&
            forall|i: int| 0 <= i < n ==> result@[i] < stop as int
        ),
        n > 0 && step < 0 ==> (
            start > stop &&
            forall|i: int| 0 <= i < n ==> result@[i] > stop as int
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error and implemented proper arange logic */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == start as int + j * step as int
    {
        let value = start as int + (i as int) * (step as int);
        
        proof {
            if n > 0 {
                lemma_bounds_maintained(start, stop, step, n, i as int);
            }
        }
        
        result.push(value as i8);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}