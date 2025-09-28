// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): derive b[(i as int)] != 0 from the forall precondition for a usize index */
proof fn b_nonzero_at_usize(b: &Vec<i32>, i: usize)
    requires
        i < b.len(),
        forall|k: int| 0 <= k < b.len() ==> b[k] != 0
{
    proof {
        let k: int = i as int;
        assert(0 <= k);
        assert(k < b.len());
        assert(b[k] != 0);
    }
}

// </vc-helpers>

// <vc-spec>
fn element_wise_modulo(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires
        a.len() == b.len(),
        a.len() > 0,
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate and push element-wise modulo with int-casted indices */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < (i as int) ==> result[j] == a[j] % b[j],
        decreases a.len() - i
    {
        assert(i < a.len());
        assert(i < b.len());
        proof {
            b_nonzero_at_usize(b, i);
            assert(b[(i as int)] != 0);
        }
        let val: i32 = a[(i as int)] % b[(i as int)];
        result.push(val);
        i = i + 1;
    }
    result
}

// </vc-code>

}
fn main() {}