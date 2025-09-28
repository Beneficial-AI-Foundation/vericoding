// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversion from i32 to int */
proof fn lemma_cube_monotonic(a: int, b: int)
    requires a <= b
    ensures a * a * a <= b * b * b
{
    assert(a * a <= b * b) by {
        if a < 0 && b >= 0 {
            assert(a * a >= 0);
            assert(b * b >= 0);
            assert(a * a <= b * b);
        } else if a >= 0 && b >= 0 {
            assert(a <= b);
            assert(a * a <= b * b);
        } else if a < 0 && b < 0 {
            let abs_a = -a;
            let abs_b = -b;
            assert(abs_a >= abs_b);
            assert(abs_a * abs_a >= abs_b * abs_b);
            assert(a * a >= b * b);
        }
    };
    assert(a * a * a <= b * b * b) by {
        if a >= 0 {
            assert(a * a * a <= b * b * b);
        } else if b <= 0 {
            let abs_a = -a;
            let abs_b = -b;
            assert(abs_a >= abs_b);
            assert(abs_a * abs_a * abs_a >= abs_b * abs_b * abs_b);
            assert(a * a * a <= b * b * b);
        } else {
            assert(a < 0 && b > 0);
            assert(a * a * a <= 0);
            assert(b * b * b >= 0);
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn cube_elements(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * a[i] * a[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type conversion error by using ghost variable */
    let mut result = Vec::new();
    let mut i: usize = 0;
    let len = a.len();
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (a[j] as int).pow(3),
        decreases len - i
    {
        ghost {
            let x = a[i] as int;
        }
        let x_val = a[i];
        let cubed = if x_val >= 0 {
            (x_val as i64 * x_val as i64).checked_mul(x_val as i64).unwrap() as i32
        } else {
            (x_val as i64 * x_val as i64).checked_mul(x_val as i64).unwrap() as i32
        };
        result.push(cubed);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}