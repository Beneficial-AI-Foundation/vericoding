// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): removed lemma keyword, made it proof fn */
spec fn valid_index(i: int, len: int) -> bool { 0 <= i < len }

proof fn index_bounds_lemma(i: int, len: int)
    requires valid_index(i, len)
    ensures 0 <= i < len
{
}
// </vc-helpers>

// <vc-spec>
fn hermemulx(c: Vec<f64>) -> (result: Vec<f64>)
    requires c.len() >= 0,
    ensures
        result.len() == c.len() + 1,
        result[0] == 0.0,
        forall|i: int| 1 <= i < c.len() ==> result[i + 1] == c[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): added decreases clause to while loop */
{
    let mut result = Vec::new();
    result.push(0.0);
    
    let mut i = 0;
    while i < c.len()
        invariant
            0 <= i <= c.len(),
            result.len() == i + 1,
            result@[0] == 0.0,
            forall|j: int| 0 <= j < i ==> result@[j + 1] == c@[j]
        decreases c.len() - i
    {
        result.push(c[i]);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}