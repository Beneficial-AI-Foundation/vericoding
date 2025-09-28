// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn cum_sum(a: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        result[0] == a[0],
        forall|i: int| 1 <= i < a.len() ==> result[i as int] as int == result[(i - 1) as int] as int + a[i as int] as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Fixed type errors and cast issues in loop and array access. Removed tracked_remove and used direct access.] */
{
    let mut result_vec: Vec<i8> = Vec::new();
    result_vec.push(a[0]);

    let mut i: nat = 1_nat;
    while i < a.len()
        invariant
            result_vec.len() == i,
            result_vec.len() >= 1,
            (i > 0) ==> (result_vec.len() > 0),
            result_vec.len() <= a.len(),
            result_vec[0] == a[0],
            forall|j: int| 1 <= j && j < i ==> result_vec[j as int] as int == result_vec[(j - 1) as int] as int + a[j as int] as int,
            0 <= i as int,
            i <= a.len(),
        decreases a.len() - i
    {
        result_vec.push((result_vec@[i - 1_nat as int] + a@[i as int]) as i8);
        i = i + 1_nat;
    }

    result_vec
}
// </vc-code>


}
fn main() {}