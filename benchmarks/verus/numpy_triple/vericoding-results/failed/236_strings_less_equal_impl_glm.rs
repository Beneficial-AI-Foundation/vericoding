// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): marked spec function as uninterpreted */
spec fn string_le(s1: String, s2: String) -> bool;

/* helper modified by LLM (iteration 5): fixed ownership by cloning strings */
fn string_le_exec(s1: String, s2: String) -> bool {
    s1 <= s2
}
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
/* code modified by LLM (iteration 5): fixed ownership by cloning strings in loop */
{
    let n = x1.len();
    let mut result = Vec::with_capacity(n);
    let mut i = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            result@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> result@[j] == string_le(x1@[j], x2@[j]),
        decreases (n as int - i as int)
    {
        result.push(string_le_exec(x1[i].clone(), x2[i].clone()));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}