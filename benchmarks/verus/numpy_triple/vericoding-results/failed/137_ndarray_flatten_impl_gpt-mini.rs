// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): push i8 into Vec<i8> with spec */
fn vec_push_i8(v: &mut Vec<i8>, x: i8)
    ensures
        v@.len() == old(v@).len() + 1,
        forall|i: int| 0 <= i < (old(v@).len() as int) ==> v@[i] == old(v@)@[i],
        v@[(old(v@).len() as int)] == x,
{
    v.push(x);
}
// </vc-helpers>

// <vc-spec>
fn flatten(mat: Vec<Vec<i8>>) -> (result: Vec<i8>)
    requires 
        mat@.len() > 0,
        forall|i: int| 0 <= i < mat@.len() ==> mat@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < mat@.len() && 0 <= j < mat@.len() ==> mat@[i].len() == mat@[j].len(),
    ensures 
        result@.len() == mat@.len() * mat@[0].len(),
        forall|r: int, c: int| 
            0 <= r < mat@.len() && 0 <= c < mat@[0].len() ==>
            result@[r * mat@[0].len() + c] == mat@[r][c]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): iterate rows and cols and push elements maintaining invariants */
{
    let rows = mat.len();
    let cols = mat[0].len();
    let mut result: Vec<i8> = Vec::new();
    let mut r: usize = 0usize;
    while r < rows
        invariant
            r <= rows,
            result@.len() == (r as int) * (cols as int),
            forall|rr: int, cc: int|
                0 <= rr < (r as int) && 0 <= cc < (cols as int) ==> result@[rr * (cols as int) + cc] == mat@[rr][cc],
        decreases rows - r
    {
        let mut c: usize = 0usize;
        while c < cols
            invariant
                c <= cols,
                result@.len() == (r as int) * (cols as int) + (c as int),
                forall|rr: int, cc: int|
                    (0 <= rr < (r as int) && 0 <= cc < (cols as int)) || (rr == (r as int) && 0 <= cc < (c as int)) ==> result@[rr * (cols as int) + cc] == mat@[rr][cc],
            decreases cols - c
        {
            let x: i8 = mat[r][c];
            vec_push_i8(&mut result, x);
            c = c + 1;
        }
        r = r + 1;
    }
    result
}
// </vc-code>

}
fn main() {}