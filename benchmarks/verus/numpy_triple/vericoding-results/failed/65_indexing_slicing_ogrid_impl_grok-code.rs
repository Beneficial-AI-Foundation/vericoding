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
    /* code modified by LLM (iteration 3): fixed compilation errors by using i64 for current to accumulate values without using int in executable code */
    let mut result: Vec<i8> = Vec::new();
    let mut current: i64 = start as i64;
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            current as int == (start as int) + (i as int) * (step as int),
            forall|j: int| 0 <= j < i ==> result@[j] == (start as int) + j * (step as int),
        decreases n - i
    {
        result.push(current as i8);
        current = current + (step as i64);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}