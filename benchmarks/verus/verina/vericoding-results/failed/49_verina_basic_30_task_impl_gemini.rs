// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed mismatched types in assert by casting usize to int */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            forall|k: int| 0 <= k < b.len() ==> b[k] != 0,
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] % b[j],
        decreases a.len() - i
    {
        assert(i < b.len());
        let val = a[i] % b[i];
        
        let i_old = i;
        result.push(val);
        
        i = i + 1;

        assert(result[i_old as int] == a[i_old as int] % b[i_old as int]);
    }
    result
}
// </vc-code>

}
fn main() {}