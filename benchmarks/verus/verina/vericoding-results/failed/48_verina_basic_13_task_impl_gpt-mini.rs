// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): cube for i32 using machine arithmetic */
fn cube_i32(x: i32) -> i32 {
    x * x * x
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
    /* code modified by LLM (iteration 4): build result Vec<i32> without using logical int casts */
    let mut res = Vec::<i32>::new();
    let mut i: usize = 0_usize;
    while i < a.len()
        invariant
            i <= a.len(),
            res.len() == i,
            forall|j: int| 0 <= j && j < (i as int) ==> res@[j] == a@[j] * a@[j] * a@[j],
        decreases
            a.len() - i
    {
        let ai = a[i];
        let cube_i = cube_i32(ai);
        res.push(cube_i);
        proof {
            assert(res.len() == i + 1);
            assert(res@[i as int] == cube_i);
            assert(cube_i == a@[i as int] * a@[i as int] * a@[i as int]);
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}