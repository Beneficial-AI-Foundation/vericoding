// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed correlation_sum_seq, as it was redundant with correlation_sum and caused confusion related to the specification. */

// </vc-helpers>

// <vc-spec>
spec fn correlation_sum(a: Seq<i32>, v: Seq<i32>, k: int) -> int
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        a[k] * v[0] + correlation_sum(a, v.skip(1), k + 1)
    }
}

fn correlate(a: Vec<i32>, v: Vec<i32>) -> (result: Vec<i32>)
    requires 
        v.len() > 0,
        v.len() <= a.len(),
    ensures
        result.len() == a.len() + 1 - v.len(),
        forall|k: int| 0 <= k < result.len() ==> 
            result[k] == correlation_sum(a@, v@, k),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed the type mismatch by calling the correct correlation_sum_seq function with proper arguments. The original spec function was `correlation_sum`, not `correlation_sum_seq`. Also, `correlation_sum` implicitly takes `a@` and `v@` for the type-correct comparison rather than `a@` and `v@` directly. */
{
    let a_len = a.len();
    let v_len = v.len();
    let result_len = a_len + 1 - v_len;
    let mut result: Vec<i32> = Vec::with_capacity(result_len);

    let mut i: usize = 0;
    while i < result_len
        invariant
            0 <= i as int,
            i as int <= result_len as int,
            result.len() == i,
            result.capacity() == result_len,
            forall|k: int| 0 <= k < i as int ==> result[k as usize] == correlation_sum(a@, v@, k),
    {
        let mut current_sum: i32 = 0;
        let mut j: usize = 0;
        while j < v_len
            invariant
                0 <= j as int,
                j as int <= v_len as int,
                j <= v_len,
                // Ensure that summation range is within bounds for a and v
                i.checked_add(j).is_some() && i + j < a_len,
                j < v_len,
        {
            current_sum = current_sum + a[i + j] * v[j];
            j = j + 1;
        }
        result.push(current_sum);

        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}