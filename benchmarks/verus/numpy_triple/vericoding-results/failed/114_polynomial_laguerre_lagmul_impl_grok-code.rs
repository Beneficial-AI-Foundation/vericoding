// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn lagmul(c1: Vec<f64>, c2: Vec<f64>) -> (result: Vec<f64>)
    requires c1.len() > 0 && c2.len() > 0,
    ensures 
        result.len() == c1.len() + c2.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] != 0.0 ==> 
                exists|j: int, k: int| 
                    0 <= j < c1.len() && 
                    0 <= k < c2.len() && 
                    j + k == i && 
                    c1[j] != 0.0 && 
                    c2[k] != 0.0)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): fixed 'by(compute)' syntax by adding space and removed trailing semicolon for proper syntax */
    let mut result: Vec<f64> = Vec::with_capacity(c1.len() + c2.len() - 1);
    let mut idx = 0;
    while idx < c1.len() + c2.len() - 1
        invariant
            idx >= 0,
            result.len() == idx,
            idx <= c1.len() + c2.len() - 1
    {
        result.push(0.0);
        idx += 1;
    }
    assert(result.len() == c1.len() + c2.len() - 1);

    let mut j = 0;
    while j < c1.len()
        invariant
            j >= 0,
            j <= c1.len(),
            forall|i: int| 0 <= i < j ==> forall|k: int| 0 <= k < c2.len() ==>
                (0 <= i + k < result.len() ==> result[i + k] == old(result)[i + k] + c1[i] * c2[k])
    {
        let mut k = 0;
        while k < c2.len()
            invariant
                k >= 0,
                k <= c2.len(),
                forall|kk: int| 0 <= kk < k ==>
                    (0 <= j + kk < result.len() ==> (result[j + kk] == old(result)[j + kk] + c1[j] * c2[kk]))
        {
            result[j + k] = result[j + k] + c1[j] * c2[k];
            k += 1;
        }
        j += 1;
    }

    proof {
        assert forall|i: int| 0 <= i < result.len() implies
            (result[i] != 0.0 ==>
                exists|jj: int, kk: int|
                    0 <= jj < c1.len() &&
                    0 <= kk < c2.len() &&
                    jj + kk == i &&
                    c1[jj] != 0.0 && c2[kk] != 0.0
            )
        by (compute);
    }

    result
}
// </vc-code>

}
fn main() {}