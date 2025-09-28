// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn cum_prod(a: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        result[0] == a[0],
        forall|i: int| 0 < i < a.len() ==> result[i] as int == result[i-1] as int * a[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): remove choose block and prove post-conditions directly */
    let mut result = Vec::<i8>::new();
    result.push(a[0]);

    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            result.len() == i,
            result@[0] == a@[0],
            forall|j: int| 0 < j < i ==> result@[j] as int == result@[j-1] as int * a@[j] as int,
        decreases a.len() - i
    {
        let prev_val = result[i-1];
        let current_val = a[i];
        let prod = prev_val * current_val;
        result.push(prod);
        
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}