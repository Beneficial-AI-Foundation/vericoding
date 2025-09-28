// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn abs_val(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>

proof fn abs_val_nonnegative(x: int)
    ensures
        abs_val(x) >= 0,
{
}

proof fn abs_val_zero_iff_zero(x: int)
    ensures
        (abs_val(x) == 0) == (x == 0),
{
}

proof fn matrix_nonempty_lemma(x: Vec<Vec<i8>>)
    requires
        x@.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] x@[i].len() > 0,
    ensures
        exists|i: int, j: int| 0 <= i < x@.len() && 0 <= j < x@[i].len(),
{
}

spec fn max_val(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

/* helper modified by LLM (iteration 5): Fixed abs_val_i8 parameter type to i8 */
spec fn abs_val_i8(x: i8) -> int {
    abs_val(x as int)
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
    /* code modified by LLM (iteration 5): Fixed inner loop invariant to use i8 parameter type */
    let mut max_abs = 0i8;
    let n = x.len();
    let m = x[0].len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            max_abs as int >= 0,
            forall|ii: int, jj: int| 
                0 <= ii < i && 0 <= jj < m ==> abs_val(x@[ii][jj] as int) <= max_abs as int,
            (max_abs as int == 0) == (forall|ii: int, jj: int| 
                0 <= ii < i && 0 <= jj < m ==> #[trigger] x@[ii][jj] == 0),
    {
        let mut j: usize = 0;
        while j < m
            invariant
                j <= m,
                max_abs as int >= 0,
                forall|ii: int, jj: int| 
                    0 <= ii < i && 0 <= jj < m ==> abs_val(x@[ii][jj] as int) <= max_abs as int,
                forall|jj: int| 0 <= jj < j ==> abs_val_i8(x[i][jj]) <= max_abs as int,
                (max_abs as int == 0) == (forall|ii: int, jj: int| 
                    0 <= ii < i && 0 <= jj < m ==> #[trigger] x@[ii][jj] == 0),
        {
            let current_abs = if x[i][j] >= 0 { x[i][j] } else { (-x[i][j]) as i8 };
            if current_abs > max_abs {
                max_abs = current_abs;
            }
            j += 1;
        }
        i += 1;
    }
    max_abs
}
// </vc-code>


}
fn main() {}