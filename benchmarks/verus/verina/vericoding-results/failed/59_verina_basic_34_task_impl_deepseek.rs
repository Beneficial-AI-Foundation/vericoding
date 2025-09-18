// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove problematic contains() usage and use Seq operations instead */
spec fn is_present_in_vec(seq: Seq<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < seq.len() && seq[i] == x
}

proof fn vec_seq_equivalence(vec: &Vec<i32>, x: i32)
    ensures
        vec.contains(&x) == vec@.contains(x)
{
}

proof fn preservation_lemma(seq: Seq<i32>, i: int, j: int, x: i32, y: i32)
    requires
        0 <= i < seq.len(),
        0 <= j < seq.len(),
        i <= j,
        seq[i] == x,
        seq[j] == y
    ensures
        exists|ri: int, rj: int| ri <= rj && seq.contains(x) && seq.contains(y)
{
}
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|x: i32| result@.contains(x) ==> is_even(x) && arr@.contains(x),
        forall|x: i32| arr@.contains(x) && is_even(x) ==> result@.contains(x),
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i <= j && 
            is_even(arr[i]) && is_even(arr[j]) ==> {
                exists|ri: int, rj: int| 0 <= ri < result.len() && 0 <= rj < result.len() && 
                    ri <= rj && result[ri] == arr[i] && result[rj] == arr[j]
            },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed contains() usage with proper verification and lemmas */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            forall|x: i32| is_present_in_vec(result@, x) ==> is_even(x) && arr@.contains(x),
            forall|x: i32| arr@.contains(x) && is_even(x) ==> is_present_in_vec(result@, x),
            forall|j: int, k: int| 0 <= j < arr.len() && 0 <= k < arr.len() && j <= k && 
                is_even(arr[j]) && is_even(arr[k]) ==> {
                    exists|rj: int, rk: int| 0 <= rj < result.len() && 0 <= rk < result.len() && 
                        rj <= rk && result@[rj] == arr[j] && result@[rk] == arr[k]
                }
    {
        if is_even(arr[i]) {
            result.push(arr[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}