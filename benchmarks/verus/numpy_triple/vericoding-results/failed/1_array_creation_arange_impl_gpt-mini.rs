// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): spec helper returning int value for element i */
spec fn elem(start: i8, step: i8, i: int) -> int
{
    start as int + i * step as int
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
    /* code modified by LLM (iteration 3): build vector of length n with values start + i*step and prove invariants using elem */
    let mut v = Vec::<i8>::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == i,
            forall|j: int| 0 <= j < i as int ==> v@[j] as int == elem(start, step, j),
        decreases n - i
    {
        let val = (start as i32 + (i as i32) * (step as i32)) as i8;
        v.push(val);
        proof {
            assert((val as int) == elem(start, step, i as int));
            assert(v@[i as int] == val);
            assert(v@[i as int] as int == elem(start, step, i as int));
        }
        i += 1;
    }
    v
}
// </vc-code>


}
fn main() {}