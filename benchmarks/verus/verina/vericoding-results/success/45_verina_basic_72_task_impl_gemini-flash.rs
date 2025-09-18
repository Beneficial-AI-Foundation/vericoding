// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed the incorrect `append_to_seq` helper to simplify the problem and avoid the `Seq::push` verification error. The main function will handle appending. */
// </vc-helpers>

// <vc-spec>
fn append(a: &Vec<i32>, b: i32) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() + 1,
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
        result[a.len() as int] == b,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed the implementation by getting rid of `append_to_seq` and directly using `Vec::push` on a cloned vector. */
{
    let mut result_vec = a.clone();
    result_vec.push(b);
    result_vec
}
// </vc-code>

}
fn main() {}