// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed integer literal syntax */
fn safe_i8_conversion(value: int) -> bool
{
    -128 <= value && value <= 127
}
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
    /* code modified by LLM (iteration 5): fixed integer literal syntax */
    let mut result: Vec<i8> = Vec::new();
    let mut i = 0;
    let mut current = start;
    
    while i < n
        invariant
            result.len() == i,
            i <= n,
            current == start + (i as i8) * step,
            forall|j: int| 0 <= j < i ==> result@[j] == start as int + j * (step as int),
            forall|j: int| 0 <= j < i ==> 
                if step > 0 { 
                    (start as int) <= result@[j] && result@[j] < (stop as int)
                } else {
                    (stop as int) < result@[j] && result@[j] <= (start as int)
                },
        decreases n - i
    {
        result.push(current);
        current = current + step;
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}