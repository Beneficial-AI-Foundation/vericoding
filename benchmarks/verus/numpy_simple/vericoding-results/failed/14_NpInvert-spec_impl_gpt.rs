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
/* helper modified by LLM (iteration 2): removed problematic lemmas and loops; no helpers needed for this implementation */
// </vc-helpers>

// <vc-spec>
fn invert(bit_width: u32, a: Vec<u32>) -> (result: Vec<u32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == (pow2(bit_width as nat) - 1) - a@[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement invert using bit mask complement directly, removing dependency on helpers */
    let n = a.len();
    let mut result_vec: Vec<u32> = Vec::new();
    result_vec.reserve(n);
    let mask: u32 = if bit_width <= 32u32 {
        if bit_width == 32u32 { u32::MAX } else { (1u32 << bit_width) - 1u32 }
    } else {
        u32::MAX
    };
    let mut i: usize = 0usize;
    while i < n
        invariant
            a.len() == n,
            result_vec.len() == i,
            0 <= i <= n,
        decreases (n - i)
    {
        let x = a[i];
        let y = (!x) & mask;
        result_vec.push(y);
        i = i + 1usize;
    }
    result_vec
}
// </vc-code>


}
fn main() {}