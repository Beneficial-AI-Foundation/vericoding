// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn pow2(n: nat) -> nat 
    decreases n
{
    if n == 0 {
        1nat
    } else {
        2nat * pow2((n - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
{
    /* helper modified by LLM (iteration 2): computes effective mask (clamped at 32 bits) */
    spec fn effective_mask(bit_width: u32) -> nat {
        if (bit_width as nat) >= 32 {
            pow2(32 as nat) - 1
        } else {
            pow2(bit_width as nat) - 1
        }
    }

    /* helper modified by LLM (iteration 2): identity spec for 32-bit max as nat */
    spec fn pow2_32_minus_1() -> nat {
        pow2(32 as nat) - 1
    }
}
// </vc-helpers>

// <vc-spec>
fn invert(bit_width: u32, a: Vec<u32>) -> (result: Vec<u32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == (pow2(bit_width as nat) - 1) - a@[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): invert each element with mask computed from bit_width */
    {
        let mut res: Vec<u32> = Vec::new();
        let n: usize = a.len();
        let mask: u32 = if bit_width >= 32 {
            u32::MAX
        } else {
            ((1u64 << (bit_width as u64)) - 1) as u32
        };
        let mut i: usize = 0;
        while i < n
            invariant
                res.len() == i,
                forall|j: int| 0 <= j < res@.len() ==> (res@[j] as nat) == effective_mask(bit_width) - a@[j],
            decreases
                n - i
        {
            let ai: u32 = a.get(i);
            res.push(mask - ai);
            i = i + 1;
        }
        res
    }
}
// </vc-code>


}
fn main() {}