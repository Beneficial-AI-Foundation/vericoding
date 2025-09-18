// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): commutativity of bitwise and */
proof fn bit_and_comm(a: u32, b: u32) ensures a & b == b & a { proof { assert((a & b) == (b & a)); } }
/* helper modified by LLM (iteration 5): and with zero yields zero */
proof fn bit_and_zero(a: u32) ensures a & 0 == 0 { proof { assert((a & 0) == 0); } }
/* helper modified by LLM (iteration 5): idempotence of bitwise and */
proof fn bit_and_idempotent(a: u32) ensures a & a == a { proof { assert((a & a) == a); } }
/* helper modified by LLM (iteration 5): and result is <= each operand */
proof fn bit_and_le(a: u32, b: u32) ensures a & b <= a && a & b <= b { proof { assert(a & b <= a); assert(a & b <= b); } }
// </vc-helpers>

// <vc-spec>
fn bitwise_and(x1: &Vec<u32>, x2: &Vec<u32>) -> (result: Vec<u32>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == (x1[i] & x2[i]) &&

            (x1[i] & x2[i]) == (x2[i] & x1[i]) &&

            (x1[i] & 0) == 0 &&

            (x1[i] & x1[i]) == x1[i] &&

            result[i] <= x1[i] && result[i] <= x2[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement element-wise bitwise and with invariants */
    let mut result: Vec<u32> = Vec::new();
    let mut i: int = 0;
    while i < (x1.len() as int)
        invariant 0 <= i && i <= (x1.len() as int)
        invariant (result.len() as int) == i
        invariant forall|j: int| 0 <= j && j < i ==> 
            result[j as usize] == (x1[j as usize] & x2[j as usize]) &&
            (x1[j as usize] & x2[j as usize]) == (x2[j as usize] & x1[j as usize]) &&
            (x1[j as usize] & 0) == 0 &&
            (x1[j as usize] & x1[j as usize]) == x1[j as usize] &&
            result[j as usize] <= x1[j as usize] && result[j as usize] <= x2[j as usize]
        decreases (x1.len() as int) - i
    {
        let v: u32 = x1[i as usize] & x2[i as usize];
        result.push(v);
        proof {
            bit_and_comm(x1[i as usize], x2[i as usize]);
            bit_and_zero(x1[i as usize]);
            bit_and_idempotent(x1[i as usize]);
            bit_and_le(x1[i as usize], x2[i as usize]);
            let j: int = i;
            assert(result[j as usize] == (x1[j as usize] & x2[j as usize]));
            assert((x1[j as usize] & x2[j as usize]) == (x2[j as usize] & x1[j as usize]));
            assert((x1[j as usize] & 0) == 0);
            assert((x1[j as usize] & x1[j as usize]) == x1[j as usize]);
            assert(result[j as usize] <= x1[j as usize]);
            assert(result[j as usize] <= x2[j as usize]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}