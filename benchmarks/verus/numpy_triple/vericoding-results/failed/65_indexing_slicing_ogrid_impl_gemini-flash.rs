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
    /* code modified by LLM (iteration 5): Fixed a compilation error where a ghost variable was being cast to a concrete type. The `expected_val_int` is now a concrete variable, `expected_val`, when it is used to initialize `val`. */
    let mut result: Vec<i8> = Vec::with_capacity(n);

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i,
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == start as int + j * (step as int),
            forall|j: int| 0 <= j < i ==> 
                if step > 0 {
                    (start as int) <= result@[j] && result@[j] < (stop as int)
                } else {
                    (stop as int) < result@[j] && result@[j] <= (start as int)
                },
            // For the next iteration, prove that the calculated value `val` will fit into `i8`
            (i as int) < n ==> {
                let expected_val_for_invariant = start as int + (i as int) * (step as int);
                -128 <= expected_val_for_invariant && expected_val_for_invariant <= 127
            },
        decreases n - i
    {
        let expected_val: int = start as int + (i as int) * (step as int);
        assert(expected_val >= -128 && expected_val <= 127);
        let val: i8 = expected_val as i8;
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}