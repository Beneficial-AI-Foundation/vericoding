// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix syntax error in proof block */
fn arange_helper(start: i8, stop: i8, step: i8, n: usize) -> (result: Vec<i8>)
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
{
    if n == 0 {
        Vec::new()
    } else {
        let mut result: Vec<i8> = Vec::with_capacity(n);
        let mut i = 0;
        while i < n
            invariant
                i <= n,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result@[j] == start as int + j * step as int,
                step > 0 ==> (start < stop && forall|j: int| 0 <= j < i ==> result@[j] < stop as int),
                step < 0 ==> (start > stop && forall|j: int| 0 <= j < i ==> result@[j] > stop as int),
            decreases n - i
        {
            let value = start as int + i * step as int;
            proof {
                if step > 0 {
                    assert(value < stop as int);
                } else {
                    assert(value > stop as int);
                }
            }
            result.push(value as i8);
            i += 1;
        }
        result
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
    /* code modified by LLM (iteration 5): call helper function */
    arange_helper(start, stop, step, n)
}
// </vc-code>


}
fn main() {}