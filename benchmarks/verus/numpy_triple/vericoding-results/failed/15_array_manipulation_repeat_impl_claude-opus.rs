// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): fixed type mismatch by casting i to int */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i * repeats,
            forall|j: int| #![trigger result[j]] 0 <= j < result.len() ==> {
                let k = j / (repeats as int);
                0 <= k < i && result[j] == a[k]
            },
        decreases a.len() - i,
    {
        let mut j = 0;
        while j < repeats
            invariant
                i < a.len(),
                j <= repeats,
                result.len() == i * repeats + j,
                forall|m: int| #![trigger result[m]] 0 <= m < result.len() ==> {
                    let k = m / (repeats as int);
                    if k < i {
                        result[m] == a[k]
                    } else {
                        k == i && m >= (i as int) * (repeats as int) && m < (i as int) * (repeats as int) + (j as int) && result[m] == a[i as int]
                    }
                },
            decreases repeats - j,
        {
            result.push(a[i]);
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}