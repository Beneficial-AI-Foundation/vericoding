// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn abs_val(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec max for ints */
spec fn max_int(a: int, b: int) -> int {
    if a >= b { a } else { b }
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
    /* code modified by LLM (iteration 5): iterate with usize counters, include decreases clauses and invariants */
    let n: usize = x.len();
    let m: usize = x[0].len();
    let mut i: usize = 0;
    let mut cur_max: i32 = 0;
    while i < n
        invariant
            i <= n,
            cur_max as int >= 0,
        decreases n - i
    {
        let mut j: usize = 0;
        while j < m
            invariant
                j <= m,
                cur_max as int >= 0,
            decreases m - j
        {
            let v: i8 = x[i][j];
            let av: i32 = if v >= 0 { v as i32 } else { -(v as i32) };
            if av > cur_max {
                cur_max = av;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    cur_max as i8
}

// </vc-code>


}
fn main() {}