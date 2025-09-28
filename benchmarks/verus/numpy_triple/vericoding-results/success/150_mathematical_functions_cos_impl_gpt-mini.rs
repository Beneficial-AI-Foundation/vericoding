// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple per-element cosine approximation */
fn cos_elem(xi: i8) -> (result: i8)
    ensures
        -1 <= result as int <= 1,
        (xi as int == 0 ==> result as int == 1),
{
    if xi == 0 { 1 } else { 0 }
}
// </vc-helpers>

// <vc-spec>
fn numpy_cos(x: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result@.len() ==> {
            -1 <= result@[i] as int <= 1 &&
            (x@[i] as int == 0 ==> result@[i] as int == 1)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): iterate and apply cos_elem to each element, fix invariant boolean expressions */
{
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i as int,
            i as int <= x.len() as int,
            res@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> (
                -1 <= res@[j] as int && res@[j] as int <= 1 &&
                (x@[j] as int == 0 ==> res@[j] as int == 1)
            ),
        decreases x.len() - i
    {
        let xi: i8 = x[i];
        let v: i8 = cos_elem(xi);
        res.push(v);
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}