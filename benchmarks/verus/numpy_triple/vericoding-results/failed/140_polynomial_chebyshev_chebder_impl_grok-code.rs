// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebder(c: Vec<i8>, scl: i8) -> (result: Vec<i8>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() - 1,
        c.len() > 1 ==> result[0] == scl * c[1],
        c.len() > 2 ==> result[1] == scl * 4 * c[2],
        forall|j: int| 2 <= j < result.len() ==>
            result[j as int] == scl * (2 * ((j + 1) as i8)) * c[(j + 1) as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented Chebyshev derivative with i64 calculations to handle overflow, proper loop indexing, and truncation back to i8 */
    let mut result: Vec<i8> = Vec::new();
    let len = c.len();
    if len > 1 {
        let first: i8 = ((scl as i64) * (c[1] as i64)) as i8;
        result.push(first);
        if len > 2 {
            let second: i8 = ((scl as i64) * 4i64 * (c[2] as i64)) as i8;
            result.push(second);
            for j in 2..(len - 1) {
                let coeff = 2i64 * ((j as i64) + 1);
                let term: i8 = ((scl as i64) * coeff * (c[j + 1] as i64)) as i8;
                result.push(term);
            }
        }
    }
    result
}
// </vc-code>

}
fn main() {}