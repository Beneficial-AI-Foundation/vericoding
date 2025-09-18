// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed incorrect path for arithmetic lemmas */
proof fn lemma_tile_mod_prop(j: int, k: int, alen: int)
    requires
        alen > 0,
        j >= 0,
        0 <= k < alen,
    ensures
        (alen * j + k) % alen == k,
{
    vstd::arithmetic::div_mod::lemma_mod_add_multiples(k, j, alen);
    vstd::arithmetic::div_mod::lemma_mod_of_nonneg_lt(k, alen);
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
{
    /* code modified by LLM (iteration 5): no code change, the fix was in a helper dependency */
    let mut result: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    let alen = a.len();

    while j < reps
        invariant
            reps > 0,
            alen > 0,
            alen == a.len(),
            0 <= j <= reps,
            (result.len() as int) == (alen as int) * (j as int),
            forall|i: int| 0 <= i < result.len() ==> result[i] == a[i % (alen as int)],
        decreases reps - j,
    {
        let mut k: usize = 0;
        while k < alen
            invariant
                0 <= k <= alen,
                alen > 0,
                alen == a.len(),
                j < reps,
                (result.len() as int) == (alen as int) * (j as int) + (k as int),
                forall|i: int| 0 <= i < result.len() ==> result[i] == a[i % (alen as int)],
            decreases alen - k,
        {
            let element = a[k];
            result.push(element);

            proof {
                lemma_tile_mod_prop(j as int, k as int, alen as int);
            }

            k = k + 1;
        }
        j = j + 1;
    }

    result
}
// </vc-code>

}
fn main() {}