// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fix type comparison between int and nat */
fn compute_mod(a: i8, b: i8) -> (result: i8)
    requires
        b != 0,
    ensures
        result == a % b,
        a == (a / b) * b + result,
        (b > 0 ==> result >= 0 && result < b),
        (b < 0 ==> result <= 0 && result > b)
{
    if b > 0 {
        let r = a % b;
        if r >= 0 {
            r
        } else {
            r + b
        }
    } else {
        let r = a % b;
        if r <= 0 {
            r
        } else {
            r + b
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn numpy_mod(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] != 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i] == x1[i] % x2[i],
        forall|i: int| 0 <= i < result.len() ==> {
            let r = #[trigger] result[i];
            let a = x1[i];
            let b = x2[i];
            /* Basic remainder property: a = floor_div(a, b) * b + r */
            a == (a / b) * b + r &&
            /* Result has same sign as divisor (when divisor is non-zero) */
            (b > 0 ==> r >= 0 && r < b) &&
            (b < 0 ==> r <= 0 && r > b)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): add triggers to quantifiers in invariant */
{
    let mut result: Vec<i8> = Vec::with_capacity(x1.len());
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == x1[j] % x2[j],
            forall|j: int| 0 <= j < i ==> {
                let r = #[trigger] result[j];
                let a = x1[j];
                let b = x2[j];
                a == (a / b) * b + r &&
                (b > 0 ==> r >= 0 && r < b) &&
                (b < 0 ==> r <= 0 && r > b)
            },
 decreases x1.len() - i
    {
        let mod_val = compute_mod(x1[i], x2[i]);
        result.push(mod_val);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}