// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] + b[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed loop invariant and overflow issue */
{
    let mut result: Vec<i32> = Vec::new();
    let len = a.len();
    result.reserve(len);

    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i as int <= len as int,
            result.len() == i,
            len == a.len(),
            len == b.len(),
            forall|j: int| 0 <= j < i as int ==> result[j] == (a[j] as int + b[j] as int) as i32,
        decreases len - i
    {
        let val_a = a[i] as int;
        let val_b = b[i] as int;
        result.push((val_a + val_b) as i32);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}