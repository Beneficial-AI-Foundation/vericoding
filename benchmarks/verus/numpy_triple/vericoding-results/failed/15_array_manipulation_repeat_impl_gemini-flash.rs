// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed */
// </vc-helpers>

// <vc-spec>
fn repeat<T: Copy>(a: Vec<T>, repeats: usize) -> (result: Vec<T>)
    requires repeats > 0,
    ensures
        result.len() == a.len() * repeats,
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
            let k = i / (repeats as int);
            0 <= k < a.len() && result[i] == a[k]
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed a compilation error regarding expected curly braces after invariant labels. */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < repeats
        invariant (
            i_inv: 0 <= i && i <= repeats,
            res_len: result.len() == (i as usize) * a.len(),
            res_content: forall|j: int| 0 <= j < result.len() ==> {
                let k = j / (a.len() as int);
                0 <= k < i && (j - k * (a.len() as int)) < a.len() && result[j] == a[j - k * (a.len() as int)]
            },
        )
        decreases repeats - i
    {
        let mut j = 0;
        while j < a.len()
            invariant (
                j_inv: 0 <= j && j <= a.len(),
                res_len_inner: result.len() == (i as usize) * a.len() + j as usize,
                res_content_inner: (forall|k_outer: int| 0 <= k_outer < (i as usize) * a.len() ==> {
                    let k = k_outer / (a.len() as int);
                    0 <= k < i && (k_outer - k * (a.len() as int)) < a.len() && result[k_outer] == a[k_outer - k * (a.len() as int)]
                })
                && (forall|k_inner: int| (i as usize) * a.len() <= k_inner < (i as usize) * a.len() + j as usize ==> {
                    result[k_inner] == a[k_inner - (i as int) * (a.len() as int)]
                }),
            )
            decreases a.len() - j
        {
            result.push(a[j]);
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}