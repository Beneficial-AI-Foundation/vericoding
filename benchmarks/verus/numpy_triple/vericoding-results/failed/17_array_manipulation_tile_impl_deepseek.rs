// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed parameter types to match usage with usize */
fn lemma_mod_range(i: int, n: nat)
    requires
        n > 0,
        i >= 0,
    ensures
        i % (n as int) >= 0,
        i % (n as int) < n as int,
{
}

fn lemma_div_mod_relation(i: int, n: nat)
    requires
        n > 0,
        i >= 0,
    ensures
        i == (n as int) * (i / (n as int)) + i % (n as int),
{
}
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
/* code modified by LLM (iteration 4): Fixed lemma call parameter types */
{
    let ghost a_len_nat = a.len();
    let ghost a_len = a_len_nat as int;
    let total_len = a.len() * reps;
    let mut result = Vec::with_capacity(total_len);
    let mut i: usize = 0;
    while i < reps
        invariant
            i <= reps,
            result.len() == i * a.len(),
            forall|j: int| 0 <= j < result.len() ==> result@[j] == a@[j % a_len],
    {
        let mut j: usize = 0;
        while j < a.len()
            invariant
                j <= a.len(),
                result.len() == i * a.len() + j,
                forall|k: int| 0 <= k < result.len() ==> result@[k] == a@[k % a_len],
        {
            result.push(a[j]);
            proof {
                lemma_mod_range(result.len() as int - 1, a_len_nat);
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