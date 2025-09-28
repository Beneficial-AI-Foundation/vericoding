// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added decreases clause */
fn create_zero_vector(size: usize) -> (result: Vec<i8>)
    requires
        size > 0,
    ensures
        result.len() == size,
        forall|i: int| 0 <= i < size ==> result@[i] == 0,
{
    let mut v = Vec::new();
    let mut idx = 0;
    while idx < size
        invariant
            v.len() == idx,
            idx <= size,
            forall|i: int| 0 <= i < idx ==> v@[i] == 0,
        decreases size - idx
    {
        v.push(0i8);
        idx += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn histogram(data: Vec<f32>, bins: Vec<f32>) -> (result: Vec<i8>)
    requires 
        bins.len() >= 2,
    ensures
        result.len() == bins.len() - 1,
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

fn histogram_helper(data: Vec<f32>, bins: Vec<f32>, hist: Vec<i8>, index: i8) -> (result: Vec<i8>)
    requires 
        bins.len() >= 2,
        hist.len() == bins.len() - 1,
    ensures
        result.len() == bins.len() - 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added bounds checks for data access */
    let mut result = create_zero_vector((bins.len() - 1) as usize);
    let mut i = 0;
    while i < data.len()
        invariant
            result.len() == bins.len() - 1,
            i <= data.len(),
        decreases data.len() - i
    {
        let mut j = 0;
        while j < bins.len() - 1
            invariant
                result.len() == bins.len() - 1,
                j <= bins.len() - 1,
                i < data.len(),
            decreases bins.len() - 1 - j
        {
            if j + 1 < bins.len() && i < data.len() && data[i] >= bins[j] && data[i] < bins[j + 1] {
                if result[j] < 127 {
                    result.set(j, result[j] + 1);
                }
                break;
            }
            j += 1;
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}