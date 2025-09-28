// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ogrid(start: i8, stop: i8, step: i8, n: usize) -> (result: Vec<i8>)
    requires 
        step != 0,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result@[i] == start as int + i * (step as int),
        forall|i: int| 0 <= i < n ==> 
            if step > 0 { 
                (start as int) <= result@[i] && result@[i] < (stop as int)
            } else {
                (stop as int) < result@[i] && result@[i] <= (start as int)
            },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): split assertions to avoid parsing error with && */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result@[j] == start as int + j * (step as int) &&
                (if step > 0 { 
                    (start as int) <= result@[j] && result@[j] < (stop as int)
                } else {
                    (stop as int) < result@[j] && result@[j] <= (start as int)
                }),
        decreases n - i
    {
        let value = (start as i64) + (i as i64) * (step as i64);
        proof {
            let current_value_spec = start as int + (i as int) * (step as int);
            assert(value as int == current_value_spec);
            if step > 0 {
                assert(start as int <= current_value_spec);
                assert(current_value_spec < stop as int);
            } else {
                assert(stop as int < current_value_spec);
                assert(current_value_spec <= start as int);
            }
            assert(value >= i8::MIN as int);
            assert(value <= i8::MAX as int);
        }
        result.push(value as i8);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}