// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define pow2 (int-based) */
spec fn pow2(shift: int) -> int {
    if shift <= 0 {
        1
    } else {
        2 * pow2(shift - 1)
    }
}

/* helper modified by LLM (iteration 5): define shift_left_int in terms of pow2 */
spec fn shift_left_int(x: int, shift: nat) -> int {
    x * pow2(shift as int)
}
// </vc-helpers>

// <vc-spec>
spec fn shift_left_int(x: int, shift: nat) -> int;

fn left_shift(a: Vec<i32>, b: Vec<u32>) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] < 64,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == shift_left_int(a[i] as int, b[i] as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement left_shift with loop and invariant relating runtime result to spec */
    let mut res: Vec<i32> = Vec::<i32>::new();
    let n = a.len();
    let mut j: usize = 0;
    while j < n
        invariant
            res.len() == j,
            forall|i: int| 0 <= i < j as int ==> res@[i] as int == shift_left_int(a@[i] as int, b@[i] as nat),
        decreases n - j
    {
        let ai: i32 = a[j];
        let bi: u32 = b[j];
        let shift: usize = bi as usize;
        let v_i128: i128 = (ai as i128) << shift;
        let out: i32 = v_i128 as i32;
        res.push(out);
        j = j + 1;
    }
    res
}
// </vc-code>


}
fn main() {}