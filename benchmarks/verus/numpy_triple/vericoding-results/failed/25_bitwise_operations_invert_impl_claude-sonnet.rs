// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma to prove sign relationship for bitwise inversion */
spec fn arithmetic_bounds(x: Vec<i32>) -> bool
{
    forall|i: int| 0 <= i < x.len() ==> x[i] > i32::MIN && x[i] < i32::MAX
}

proof fn lemma_invert_sign_relationship(x: i32)
    requires x != -1
    ensures (x > 0) <==> (-(x + 1) < 0)
{
    if x > 0 {
        assert(x + 1 > 1);
        assert(-(x + 1) < -1);
        assert(-(x + 1) < 0);
    } else {
        assert(x < 0);
        assert(x <= -2);
        assert(x + 1 <= -1);
        assert(-(x + 1) >= 1);
        assert(-(x + 1) >= 0);
    }
}
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
    /* code modified by LLM (iteration 5): added proof calls to establish sign relationship */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            result.len() == i,
            i <= x.len(),
            forall|j: int| 0 <= j < i ==> result[j] == -(x[j] + 1),
        decreases x.len() - i
    {
        let x_val = x[i];
        let inverted = if x_val == i32::MAX {
            i32::MIN
        } else {
            -(x_val + 1)
        };
        
        proof {
            if x_val != -1 {
                lemma_invert_sign_relationship(x_val);
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