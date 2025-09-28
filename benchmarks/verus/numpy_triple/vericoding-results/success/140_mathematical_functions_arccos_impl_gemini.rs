// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [Retained original implementation] */
fn arccos_map(val: i8) -> (res: i8)
    requires
        -1 <= val as int && val as int <= 1,
    ensures
        0 <= res as int && res as int <= 3,
        val as int == 1 ==> res as int == 0,
        val as int == -1 ==> res as int == 3,
{
    if val == 1 {
        0
    } else if val == -1 {
        3
    } else {
        2
    }
}
// </vc-helpers>

// <vc-spec>
fn arccos(x: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> -1 <= x[i] as int && x[i] as int <= 1,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> (
            0 <= result[i] as int && 
            result[i] as int <= 3 &&
            (x[i] as int == -1 ==> result[i] as int == 3) &&
            (x[i] as int == 1 ==> result[i] as int == 0)
        ),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): [Added invariant to satisfy helper precondition] */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> (
                0 <= result@[j] as int && result@[j] as int <= 3 &&
                (x@[j] as int == -1 ==> result@[j] as int == 3) &&
                (x@[j] as int == 1 ==> result@[j] as int == 0)
            ),
            forall|k: int| 0 <= k < x.len() ==> -1 <= x@[k] as int && x@[k] as int <= 1,
        decreases x.len() - i
    {
        let mapped_val = arccos_map(x[i]);
        result.push(mapped_val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}