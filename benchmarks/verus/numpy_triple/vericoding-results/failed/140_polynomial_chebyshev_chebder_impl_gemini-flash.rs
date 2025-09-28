// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix compiler error. */
fn multiply_i8(a: i8, b: i8) -> i8
    ensures
        (a as i64 * b as i64) >= i8::MIN as i64,
        (a as i64 * b as i64) <= i8::MAX as i64,
        (a as i64 * b as i64) == result as i64,
{
    (a as i32 * b as i32) as i8
}
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
/* code modified by LLM (iteration 5): Correct the condition for result[0] and result[1] in the loop invariant to properly match the output. */
{
    let n = c.len();
    let mut result: Vec<i8> = Vec::new();

    if n <= 1 {
        return result;
    }

    result.reserve((n - 1) as usize);

    let mut j: nat = 0;
    while j < n - 1
        invariant
            0 <= j,
            j <= n - 1,
            result.len() == j,
            result.spec_len() == j,
            forall|k: int| 0 <= k < j ==> {
                if k == 0 {
                    result.wf(k as nat) && c.wf(1 as nat) && result[k as int] == multiply_i8(scl, c[1])
                } else if k == 1 {
                    if c.len() >= 3 {
                        result.wf(k as nat) && c.wf(2 as nat) && result[k as int] == multiply_i8(multiply_i8(scl, 4), c[2])
                    } else {
                        true // Should not happen given outer guard.
                    }
                } else {
                    result.wf(k as nat) && c.wf((k + 1) as nat) && result[k as int] == multiply_i8(multiply_i8(scl, (2 * ((k + 1) as i8))), c[(k + 1) as usize])
                }
            },
        decreases (n - 1) - j
    {
        if j == 0 {
            result.push(multiply_i8(scl, c[1 as usize]));
        } else if j == 1 {
            result.push(multiply_i8(multiply_i8(scl, 4), c[2 as usize]));
        } else {
            result.push(multiply_i8(multiply_i8(scl, (2 * ((j + 1) as i8))), c[(j + 1) as usize]));
        }
        j = j + 1;
    }

    result
}
// </vc-code>

}
fn main() {}