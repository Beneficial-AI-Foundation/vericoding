// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 2): fixed compilation by wrapping in function body braces */
    let mut result: Vec<i8> = Vec::with_capacity(n);
    let mut current: i8 = start;
    if n > 0 {
        let mut i: usize = 0;
        while i < n
            invariant
                result.len() == i,
                i <= n,
                forall|j: int| 0 <= j < result.len() ==> result@[j] == start as int + j as int * step as int,
            decreases n - i
        {
            result.push(current);
            current = current + step;
            i = i + 1;
        }
    }
    result
}
// </vc-code>


}
fn main() {}