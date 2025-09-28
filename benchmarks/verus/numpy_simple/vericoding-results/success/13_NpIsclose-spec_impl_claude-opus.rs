// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (-(tol as int) < (a[j] as int) - (b[j] as int) && (a[j] as int) - (b[j] as int) < (tol as int)),
        decreases a.len() - i
    {
        let diff = (a[i] as i32) - (b[i] as i32);
        let is_close = -(tol as i32) < diff && diff < (tol as i32);
        result.push(is_close);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}