// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [used i16 to avoid overflow and fix compile error] */
fn is_close_i8(a: i8, b: i8, tol: i8) -> (res: bool)
    requires
        tol > 0,
    ensures
        res == (-(tol as int) < (a as int) - (b as int) && (a as int) - (b as int) < (tol as int)),
{
    let diff = (a as i16) - (b as i16);
    let tol_i16 = tol as i16;
    -tol_i16 < diff && diff < tol_i16
}
// </vc-helpers>

// <vc-spec>
fn np_isclose(a: Vec<i8>, b: Vec<i8>, tol: i8) -> (result: Vec<bool>)
    requires 
        a.len() > 0,
        a.len() == b.len(),
        tol > 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i] == (-(tol as int) < (a[i] as int) - (b[i] as int) && (a[i] as int) - (b[i] as int) < (tol as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): [changed loop counter to usize to fix compile error] */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            tol > 0,
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> 
                result[j] == (-(tol as int) < (a[j] as int) - (b[j] as int) && (a[j] as int) - (b[j] as int) < (tol as int)),
        decreases a.len() - i
    {
        let close = is_close_i8(a[i], b[i], tol);
        result.push(close);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}