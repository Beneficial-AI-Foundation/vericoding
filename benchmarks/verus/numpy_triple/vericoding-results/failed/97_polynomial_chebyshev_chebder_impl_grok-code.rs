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
{
    let mut result = Vec::new();
    let c_len = c.len();
    for i in 0..(c_len - 1) {
        if i == 0 {
            if c_len > 1 {
                result.push(scl * c[i + 1]);
            }
        } else if i == 1 {
            if c_len > 2 {
                result.push(scl * 4 * c[i + 1]);
            } else {
                result.push(0);
            }
        } else {
            result.push(scl * (2 * (i as i32 + 1)) * c[i + 1]);
        }
    }
    result
}
// </vc-code>

}
fn main() {}