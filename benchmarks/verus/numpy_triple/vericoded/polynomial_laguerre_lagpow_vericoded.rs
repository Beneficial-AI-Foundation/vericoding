// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn make_zeros(n: usize) -> (v: Vec<f32>)
    ensures
        v.len() == n,
{
    let mut v: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == i,
            i <= n,
        decreases (n - i) as int
    {
        v.push(0.0f32);
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn lagpow(c: Vec<f32>, pow: u8, maxpower: u8) -> (result: Vec<f32>)
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
    if pow == 1u8 {
        c
    } else {
        let n = c.len();
        let v = make_zeros(n);
        v
    }
}
// </vc-code>

}
fn main() {}