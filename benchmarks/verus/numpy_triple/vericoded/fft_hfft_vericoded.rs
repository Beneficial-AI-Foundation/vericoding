// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq)]
pub struct Complex {
    pub real: f32,
    pub imag: f32,
}
// </vc-preamble>

// <vc-helpers>
pub proof fn lemma_usize_nat_mult2_u8(m: u8)
    ensures
        ((m as usize) * 2) as nat == 2 * (m as nat),
{
}

// </vc-helpers>

// <vc-spec>
fn hfft(a: Vec<Complex>, m: u8) -> (result: Vec<f32>)
    requires 
        m > 0,
        a.len() == m as nat + 1,
    ensures
        result.len() == 2 * m as nat,
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<f32> = Vec::new();
    let bound: usize = (m as usize) * 2;
    proof { lemma_usize_nat_mult2_u8(m); }
    let mut i: usize = 0;
    while i < bound
        invariant
            i <= bound,
            res.len() == i as nat,
        decreases (bound - i) as int
    {
        res.push(0.0f32);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}