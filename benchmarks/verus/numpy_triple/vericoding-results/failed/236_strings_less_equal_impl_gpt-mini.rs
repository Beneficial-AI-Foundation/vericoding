// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): identity for bool */
spec fn bool_id(b: bool) -> bool { b }
// </vc-helpers>

// <vc-spec>
spec fn string_le(s1: String, s2: String) -> bool;

fn less_equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1@.len() == x2@.len(),
    ensures 
        result@.len() == x1@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == string_le(x1@[i], x2@[i]),
        forall|i: int| 0 <= i < result@.len() ==> (result@[i] == true <==> string_le(x1@[i], x2@[i])),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result@.len() ==> result@[i] == true,
        forall|i: int| 0 <= i < result@.len() ==> (string_le(x1@[i], x2@[i]) && string_le(x2@[i], x1@[i])) ==> x1@[i] == x2@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate with usize index and use runtime indexing, avoid nat/int in local vars */
    let mut res: Vec<bool> = Vec::with_capacity(x1.len());
    let len = x1.len();
    let mut i: usize = 0;
    while i < len
        invariant
            res@.len() == i as int,
            forall|j: int| 0 <= j < res@.len() ==> res@[j] == string_le(x1@[j], x2@[j]),
        decreases (len - i),
    {
        let v = string_le(x1[i].clone(), x2[i].clone());
        res.push(v);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}