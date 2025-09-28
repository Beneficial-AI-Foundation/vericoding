// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_int(x: int) -> int {
    if x < 0 { -x } else { x }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn abs(a: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] as int == abs_int(a[i] as int),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to loop */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == abs_int(a[j] as int),
        decreases a.len() - i
    {
        let val = a[i];
        let abs_val = if val < 0 {
            -val
        } else {
            val
        };
        result.push(abs_val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}