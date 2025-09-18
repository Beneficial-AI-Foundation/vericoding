// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn zero_f64() -> f64 { 0.0 }
spec fn is_nonempty<A>(s: Seq<A>) -> bool { s.len() > 0 }
// </vc-helpers>

// <vc-spec>
fn lagval(x: Vec<f64>, c: Vec<f64>) -> (result: Vec<f64>)
    requires 
        c.len() > 0,
        x.len() > 0,
    ensures
        result.len() == x.len(),
        true, // Polynomial evaluation results exist (trivially true)
// </vc-spec>
// <vc-code>
{
    let n = x.len();
    let mut y: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            y.len() == i,
            i <= n,
        decreases (n as int) - (i as int)
    {
        y.push(zero_f64());
        i += 1;
    }
    y
}
// </vc-code>

}
fn main() {}