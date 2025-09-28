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
fn pow2_exec(n: u32) -> (result: u32)
    requires
        n < 32,
    ensures
        result as nat == pow2(n as nat),
{
    let mut i: u32 = 0;
    let mut res: u32 = 1;
    while i < n
        invariant
            n < 32,
            i <= n,
            res as nat == pow2(i as nat),
        decreases n - i
    {
        res = res * 2;
        i = i + 1;
    }
    res
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
    let mut result: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (pow2(bit_width as nat) - 1) - a@[j],
        decreases a.len() - i
    {
        let val = a[i];
        let inverted_val: u32;
        if bit_width == 32 {
            proof {
                assert(pow2(32) == (u32::MAX as nat) + 1);
            }
            inverted_val = u32::MAX - val;
        } else {
            // The ensures clause is unsatisfiable if bit_width > 32.
            // Thus, we know bit_width < 32 in this branch.
            let p = pow2_exec(bit_width);
            // The ensures clause also implies val < pow2(bit_width), so this subtraction is safe.
            inverted_val = p - 1 - val;
        }
        result.push(inverted_val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}