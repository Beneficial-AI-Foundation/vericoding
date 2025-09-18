// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): antisymmetry lemma for >= on i32 */
proof fn ge_antisym_i32(a: i32, b: i32)
    ensures (a >= b && b >= a) ==> a == b
{
    if a >= b && b >= a {
        assert(a == b);
    }
}

/* helper modified by LLM (iteration 2): spec predicate for >= as a bool */
spec fn ge_bool(a: i32, b: i32) -> bool { a >= b }
// </vc-helpers>

// <vc-spec>
fn numpy_greater_equal(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> (result[i] <==> x1@[i] >= x2@[i]),

        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true,

        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] == true && x2@[i] >= x1@[i]) ==> x1@[i] == x2@[i],

        forall|i: int| 0 <= i < result.len() ==> (result[i] == true || result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implemented element-wise >= with loop; moved int usage into proof block to satisfy ghost restrictions */
    let n = x1.len();
    let mut result_vec: Vec<bool> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            result_vec.len() == i,
            i <= n,
            x1.len() == n,
            x2.len() == n,
            forall|j: int| 0 <= j < i ==> (result_vec@[j] <==> x1@[j] >= x2@[j]),
        decreases n - i
    {
        let b = x1[i] >= x2[i];
        result_vec.push(b);

        proof {
            assert(result_vec@[i as int] == b);
        }

        i += 1;
    }

    result_vec
}
// </vc-code>

}
fn main() {}