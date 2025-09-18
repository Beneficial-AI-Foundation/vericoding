// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed as no helpers are needed. */
// </vc-helpers>

// <vc-spec>
fn tile(a: Vec<i32>, reps: usize) -> (result: Vec<i32>)
    requires 
        reps > 0,
        a.len() > 0,
    ensures
        result.len() == a.len() * reps,
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i % (a.len() as int)],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replaced `view_nat_index` with `@` for sequence indexing. */
{
    let a_len: usize = a.len();
    let reps_u: usize = reps;

    // result_len will be concrete and cannot be negative
    let result_len: usize = a_len * reps_u;

    let mut result: Vec<i32> = Vec::with_capacity(result_len);

    let mut i: usize = 0;
    while i < result_len
        invariant
            i <= result_len,
            result.len() == i,
            a_len > 0,
            reps_u > 0, // from requires clause
            forall|j: int| 0 <= j < i ==> result@[j as int] == a@((j as int) % (a_len as int)),
        decreases result_len - i,
    {
        let index_in_a: usize = i % a_len;
        proof {
            assert(0 <= i);
            assert(0 < a_len); // from requires
            assert(index_in_a < a_len); // by properties of %, 0 <= a % b < b if b > 0
            assert(0 <= index_in_a); // same reason
        }

        result.push(a[index_in_a]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}