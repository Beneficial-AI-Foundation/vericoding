// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed loop invariant to initialize current_max to v[0] and i to 1 for the first iteration */
fn max_vec_i8(v: &Vec<i8>) -> (max_val: i8)
    requires
        v.len() > 0,
    ensures
        exists|i: int| #![trigger v@.index(i)] 0 <= i < v@.len() && max_val as int == v@[i],
        forall|i: int| #![trigger v@.index(i)] 0 <= i < v@.len() ==> v@[i] <= max_val as int,
{
    let mut i = 1;
    let mut current_max = v[0];

    while i < v.len()
        invariant
            1 <= i && i <= v.len(),
            exists|j: int| 0 <= j < i && current_max as int == v@[j],
            forall|j: int| 0 <= j < i ==> v@[j] <= current_max as int,
        decreases v.len() - i
    {
        if v[i] > current_max {
            current_max = v[i];
        }
        i = i + 1;
    }
    current_max
}
// </vc-helpers>

// <vc-spec>
fn max(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures 
        exists|i: int| 0 <= i < a@.len() && result as int == a@[i],
        forall|i: int| 0 <= i < a@.len() ==> a@[i] <= result as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): calls the helper function to find the maximum in the vector */
{
    let result = max_vec_i8(&a);
    result
}
// </vc-code>


}
fn main() {}