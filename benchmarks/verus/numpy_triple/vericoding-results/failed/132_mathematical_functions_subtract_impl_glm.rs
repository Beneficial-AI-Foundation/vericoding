// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): moved int conversions to proof block to avoid compilation errors */
fn subtract_helper(a: i8, b: i8) -> (result: i8)
    ensures
        result == a - b,
        b == 0 ==> result == a,
        a == b ==> result == 0,
        result == -(b - a)
{
    let result = a - b;
    proof {
        let a_int = a as int;
        let b_int = b as int;
        let result_int = result as int;
        assert(result_int == a_int - b_int);
        if b == 0 {
            assert(result_int == a_int);
        }
        if a == b {
            assert(result_int == 0);
        }
        assert(a_int - b_int == -(b_int - a_int));
        assert(result_int == -(b_int - a_int));
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn subtract(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result@[i] == x1@[i] - x2@[i],
        /* Sanity check: subtracting zero preserves the original value */
        forall|i: int| 0 <= i < result.len() && x2@[i] == 0 ==> result@[i] == x1@[i],
        /* Sanity check: subtracting a value from itself yields zero */
        forall|i: int| 0 <= i < result.len() && x1@[i] == x2@[i] ==> result@[i] == 0,
        /* Anti-commutativity property */
        forall|i: int| 0 <= i < result.len() ==> result@[i] == -(x2@[i] - x1@[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): changed index type to usize and used ghost conversion in invariants */
{
    let mut result = Vec::with_capacity(x1.len());
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            0 <= i as int <= x1.len() as int,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] == x1@[j] - x2@[j],
            forall|j: int| 0 <= j < i as int && x2@[j] == 0 ==> result@[j] == x1@[j],
            forall|j: int| 0 <= j < i as int && x1@[j] == x2@[j] ==> result@[j] == 0,
            forall|j: int| 0 <= j < i as int ==> result@[j] == -(x2@[j] - x1@[j])
        decreases (x1.len() as int) - (i as int)
    {
        result.push(subtract_helper(x1[i], x2[i]));
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}