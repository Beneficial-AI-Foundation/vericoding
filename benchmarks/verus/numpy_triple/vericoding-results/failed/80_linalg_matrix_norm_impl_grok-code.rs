// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn abs_val(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
fn abs_val_exec(x: i8) -> (res: i8)
    requires
        x != -128,
    ensures
        res as int == abs_val(x as int),
{
    if x < 0 { -x } else { x }
}
// </vc-helpers>

// <vc-spec>
fn matrix_norm(x: Vec<Vec<i8>>) -> (result: i8)
    requires 
        x@.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] x@[i].len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] x@[i].len() == x@[0].len(),
    ensures
        result as int >= 0,
        (result as int == 0) == (forall|i: int, j: int| 
            0 <= i < x@.len() && 0 <= j < x@[i].len() ==> #[trigger] x@[i][j] == 0),
        forall|i: int, j: int| 
            0 <= i < x@.len() && 0 <= j < x@[i].len() ==> abs_val(#[trigger] x@[i][j] as int) <= result as int,
        (exists|i: int, j: int| 
            0 <= i < x@.len() && 0 <= j < x@[i].len() && #[trigger] x@[i][j] != 0) ==> result as int > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed types by using usize for indices */
    let mut max: i8 = abs_val_exec(x[0][0]);
    let mut ii: usize = 0;
    while ii < x@.len() as usize
        invariant
            ii <= x@.len(),
            max as int >= 0,
            forall |k: usize, l: usize| k < ii && l < x@[k].len() ==> abs_val(x@[k][l] as int) <= max as int,
            forall |k: usize| k < x@.len() ==> forall |l: usize| l < x@[k].len() ==> x@[k][l] != -128,
        decreases x@.len() as usize - ii
    {
        let mut jj: usize = 0;
        while jj < x@[ii].len() as usize
            invariant
                ii < x@.len(),
                jj <= x@[ii].len(),
                max as int >= 0,
                forall |k: usize, l: usize| k < ii && l < x@[k].len() ==> abs_val(x@[k][l] as int) <= max as int,
                forall |l: usize| l < jj ==> abs_val(x@[ii][l] as int) <= max as int,
                forall |k: usize| k < x@.len() ==> forall |l: usize| l < x@[k].len() ==> x@[k][l] != -128,
            decreases x@[ii].len() as usize - jj
        {
            let val = x[ii][jj];
            let abs_val_v = abs_val_exec(val);
            if abs_val_v > max {
                max = abs_val_v;
            }
            jj = jj + 1;
        }
        ii = ii + 1;
    }
    max
}
// </vc-code>


}
fn main() {}