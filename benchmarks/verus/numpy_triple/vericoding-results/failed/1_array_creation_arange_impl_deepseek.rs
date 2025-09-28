// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn prove_arange_step_condition(start: i8, stop: i8, step: i8, n: usize)
    requires step != 0
    ensures
        n == 0 ==> ((step > 0 && start >= stop) || (step < 0 && start <= stop)),
        n > 0 && step > 0 ==> start < stop,
        n > 0 && step < 0 ==> start > stop
{
    if step > 0 {
        if n > 0 {
            assert(start < stop);
        }
    } else {
        if n > 0 {
            assert(start > stop);
        }
    }
}

/* helper modified by LLM (iteration 5): Added proof keyword to make function executable in proof mode */
proof fn prove_valid_i8_conversion()
    ensures
        forall|x: int| i8::MIN as int <= x <= i8::MAX as int ==> (x as i8) as int == x
{
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
    /* code modified by LLM (iteration 5): Added decreases clause to while loop */
    assert(step != 0);
    
    let mut result = Vec::new();
    let mut current: i64 = start as i64;
    let step_i64 = step as i64;
    let mut idx: usize = 0;
    
    while idx < n
        invariant
            result.len() == idx,
            idx <= n,
            current == start as i64 + (idx as i64) * step_i64,
            forall|i: int| 0 <= i < idx ==> (
                result@[i] as int == start as int + i * step as int
            )
        decreases n - idx
    {
        result.push(current as i8);
        current = current + step_i64;
        idx = idx + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}