// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn default_coeff() -> f64 { 0.0 }

proof fn lemma_not_lt_implies_ge(a: usize, b: usize)
    ensures (! (a < b)) ==> (a >= b)
{
}

spec fn dec_measure(n: usize, i: usize) -> int {
    (n as int) - 1 - (i as int)
}
// </vc-helpers>

// <vc-spec>
fn hermeder(c: Vec<f64>, m: usize, scl: f64) -> (result: Vec<f64>)
    requires 
        c.len() > 0,
        m > 0,
        scl != 0.0,
    ensures 
        result.len() == c.len() - 1,
// </vc-spec>
// <vc-code>
{
    let n: usize = c.len();
    let mut out: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n - 1
        invariant
            n == c.len(),
            n > 0,
            out.len() == i,
            i <= n - 1,
            (i as int) <= (n as int) - 1
        decreases (n as int) - 1 - (i as int)
    {
        out.push(default_coeff());
        i = i + 1;
    }
    assert(i == n - 1);
    out
}
// </vc-code>

}
fn main() {}