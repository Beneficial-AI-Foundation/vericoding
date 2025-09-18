// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed integer cast to use i32 type instead of int */
    proof fn chebder_helper0(j: nat, c: Seq<i32>, scl: i32) -> (res: i32)
        requires
            j < c.len(),
        ensures
            res == (if j == 0 { scl * c[1] } else if j == 1 { scl * 4 * c[2] } else { scl * (2 * ((j as i32) + 1)) * c[j + 1] })
    {
        if j == 0 {
            scl * c[1]
        } else if j == 1 {
            scl * 4 * c[2]
        } else {
            scl * (2 * ((j as i32) + 1)) * c[j + 1]
        }
    }
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
/* code modified by LLM (iteration 5): Fixed integer casts to use i32 type instead of int */
{
    let n = c.len();
    let mut result = Vec::new();
    let mut i = 0;
    while i < n - 1
        invariant
            result.len() == i,
            i <= n - 1,
            forall|j: int| 0 <= j < i ==> result[j] == chebder_helper0(j as nat, c@, scl),
    {
        let val = if i == 0 {
            scl * c[1]
        } else if i == 1 {
            scl * 4 * c[2]
        } else {
            scl * (2 * ((i as i32) + 1)) * c[i + 1]
        };
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}