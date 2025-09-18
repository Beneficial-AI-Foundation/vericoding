// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed, helper is correct. */
proof fn bitwise_not_is_neg_plus_one(x: i32) ensures !x == -(x + 1) { assert(!x == -(x + 1)) by(bit_vector); }
// </vc-helpers>

// <vc-spec>
fn invert(x: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] == -(x[i] + 1),
        forall|i: int| 0 <= i < x.len() && x[i] == 0 ==> result[i] == -1,
        forall|i: int| 0 <= i < x.len() && x[i] == -1 ==> result[i] == 0,
        forall|i: int| 0 <= i < x.len() && x[i] != -1 ==> (x[i] > 0 <==> result[i] < 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added assertion with bit_vector proof to satisfy failing invariant */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> result[j] == -(x[j] + 1),
            forall|j: int| 0 <= j < (i as int) && x[j] == 0 ==> result[j] == -1,
            forall|j: int| 0 <= j < (i as int) && x[j] == -1 ==> result[j] == 0,
            forall|j: int| 0 <= j < (i as int) && x[j] != -1 ==> (x[j] > 0 <==> result[j] < 0),
        decreases x.len() - i,
    {
        let val = x[i];
        let inverted_val = !val;

        proof {
            bitwise_not_is_neg_plus_one(val);
            if val != -1 {
                assert((val > 0) <==> (inverted_val < 0)) by(bit_vector);
            }
        }

        result.push(inverted_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}