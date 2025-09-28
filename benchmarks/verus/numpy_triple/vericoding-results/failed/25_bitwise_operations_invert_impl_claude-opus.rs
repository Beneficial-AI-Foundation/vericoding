// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed logic error in proof for negative values */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == -(x[j] + 1),
            forall|j: int| 0 <= j < i && x[j] != -1 ==> (x[j] > 0 <==> result[j] < 0),
        decreases x.len() - i
    {
        let val = x[i];
        let inverted = if val == i32::MAX {
            i32::MIN
        } else {
            -(val + 1)
        };
        
        proof {
            assert(inverted == -(val + 1));
            if val != -1 {
                if val > 0 {
                    assert(val >= 1);
                    assert(val + 1 >= 2);
                    assert(-(val + 1) <= -2);
                    assert(inverted < 0);
                } else {
                    assert(val < 0);
                    assert(val < -1);
                    assert(val + 1 <= -1);
                    assert(-(val + 1) >= 1);
                    assert(inverted > 0);
                }
            }
        }
        
        result.push(inverted);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}