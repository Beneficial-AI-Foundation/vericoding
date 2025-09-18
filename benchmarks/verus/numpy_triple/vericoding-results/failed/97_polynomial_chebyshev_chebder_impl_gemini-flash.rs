// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebder(c: Vec<i32>, scl: i32) -> (result: Vec<i32>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() - 1,
        c.len() > 1 ==> result[0] == scl * c[1],
        c.len() > 2 ==> result[1] == scl * 4 * c[2],
        forall|j: int| 2 <= j < result.len() ==>
            result[j] == scl * (2 * ((j + 1) as i32)) * c[j + 1],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed ghost types `int` and `nat` to `usize` for concrete code. */
{
    let n_usize = c.len();

    if n_usize <= 1 {
        return Vec::new();
    }

    let mut result: Vec<i32> = Vec::with_capacity(n_usize - 1);

    if n_usize > 1 {
        result.push(scl * c[1]);
    }

    if n_usize > 2 {
        result.push(scl * 4 * c[2]);
    }

    if n_usize > 3 {
        let mut j: usize = 2;
        while j < n_usize - 1
            invariant
                2 <= j,
                j <= n_usize - 1,
                result.len() == j + 1
        {
            result.push(scl * (2 * ((j + 1) as i32)) * c[j + 1]);
            j = j + 1;
        }
    }

    result
}
// </vc-code>

}
fn main() {}