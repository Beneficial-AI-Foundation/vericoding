// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermint(c: Vec<f32>, m: u8, k: Vec<f32>, lbnd: f32, scl: f32) -> (result: Vec<f32>)
    requires 
        m > 0,
        k.len() == m as nat,
        c.len() > 0,
    ensures 
        result.len() == c.len() + m as nat,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed compilation error by using usize for loop counter instead of int, as int cannot be used in executable code */
    proof {
        assert(m > 0);
        assert(k.len() == m as nat);
        assert(c.len() > 0);
    }
    let mut result = c.clone();
    let mut i: usize = 0;
    while i < (m as usize)
        invariant
            i >= 0,
            i <= (m as usize),
            result.len() == c.len() + i as nat,
        decreases (m as usize) - i
    {
        result.push(0.0);
        i = i + 1;
    }
    proof {
        assert(i == (m as usize));
        assert(result.len() == c.len() + (m as nat));
    }
    result
}
// </vc-code>

}
fn main() {}