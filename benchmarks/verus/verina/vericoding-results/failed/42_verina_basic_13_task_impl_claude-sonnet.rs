// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified safe_cube and strengthened cube_no_overflow proof */
spec fn safe_cube(x: i32) -> bool {
    x >= -1290 && x <= 1290
}

proof fn cube_no_overflow(x: int)
    requires x >= i32::MIN && x <= i32::MAX && safe_cube(x as i32)
    ensures x * x * x <= i32::MAX && x * x * x >= i32::MIN
{
    assert(x >= -1290 && x <= 1290);
    assert(-1290 * -1290 * -1290 >= i32::MIN);
    assert(1290 * 1290 * 1290 <= i32::MAX);
    if x >= 0 {
        assert(x * x * x >= 0);
        assert(x * x * x <= 1290 * 1290 * 1290);
    } else {
        assert(x * x * x <= 0);
        assert(x * x * x >= -1290 * -1290 * -1290);
    }
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
    /* code modified by LLM (iteration 5): added safe_cube precondition check before operations */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] * a[j] * a[j],
        decreases a.len() - i
    {
        let x = a[i];
        assert(safe_cube(x));
        proof {
            cube_no_overflow(x as int);
        }
        let square = x * x;
        let cube = square * x;
        result.push(cube);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}