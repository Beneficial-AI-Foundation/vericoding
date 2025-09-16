// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added checked multiplication helper */
fn checked_mul_usize(a: usize, b: usize) -> (result: Option<usize>)
    ensures
        result.is_some() ==> result.unwrap() == a * b,
        result.is_none() ==> a * b > usize::MAX,
{
    a.checked_mul(b)
}
// </vc-helpers>

// <vc-spec>
fn derivative(xs: &Vec<usize>) -> (ret: Option<Vec<usize>>)

    ensures
        ret.is_some() ==> xs@.len() == 0 || xs@.map(|i: int, x| i * x).skip(1)
            =~= ret.unwrap()@.map_values(|x| x as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed arithmetic overflow and invariant issues */
    if xs.len() == 0 {
        return Some(Vec::new());
    }
    
    let mut result = Vec::new();
    
    for i in 1..xs.len()
        invariant
            result@.len() == i - 1,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == (j + 1) * xs@[j + 1],
    {
        let derivative_val_opt = checked_mul_usize(i, xs[i]);
        if derivative_val_opt.is_none() {
            return None;
        }
        let derivative_val = derivative_val_opt.unwrap();
        result.push(derivative_val);
    }
    
    Some(result)
}
// </vc-code>

}
fn main() {}