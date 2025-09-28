// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove duplicate spec declaration and fix compilation error */
spec fn shift_left_int(x: int, shift: nat) -> int {
    x * (2.pow(shift))
}

proof fn shift_left_int_proof(x: int, shift: nat)
    ensures
        shift_left_int(x, shift) == x * (2.pow(shift)),
{
}
// </vc-helpers>

// <vc-spec>
spec fn shift_left_int(x: int, shift: nat) -> int;

fn left_shift(a: Vec<i32>, b: Vec<u32>) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] < 64,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == shift_left_int(a[i] as int, b[i] as nat),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Implement vector shifting with proper verification */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == shift_left_int(a@[j] as int, b@[j] as nat),
        decreases a.len() - i,
    {
        let shift_val = b.index(i) as u32;
        let shifted = a.index(i) << shift_val;
        result.push(shifted);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}