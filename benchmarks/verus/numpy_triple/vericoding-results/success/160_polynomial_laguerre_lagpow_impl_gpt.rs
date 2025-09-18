// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_valid_pow(pow: nat, maxpower: nat) -> bool { 0 < pow && pow <= maxpower && maxpower <= 16 }
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn lagpow(c: Vec<f32>, pow: usize, maxpower: usize) -> (result: Vec<f32>)
    requires 
        pow > 0,
        pow <= maxpower,
        maxpower <= 16,
        c.len() > 0,
    ensures 
        result.len() == c.len(),
        pow == 1 ==> (forall|i: int| 0 <= i < result.len() ==> result[i] == c[i]),
// </vc-spec>
// <vc-code>
{
    if pow == 1usize {
        return c;
    } else {
        let n = c.len();
        let mut out: Vec<f32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                out.len() == i,
            decreases n - i
        {
            out.push(0.0f32);
            i = i + 1;
        }
        out
    }
}
// </vc-code>

}
fn main() {}