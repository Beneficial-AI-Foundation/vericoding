// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min_usize(a: usize, b: usize) -> usize { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn legder(c: Vec<f64>, m: usize, scl: f64) -> (result: Vec<f64>)
    requires c.len() >= 1,
    ensures
        result.len() == if c.len() > m { c.len() - m } else { 1 },
        m == 0 ==> (result.len() == c.len() && forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),
        m >= c.len() ==> result.len() == 1,
// </vc-spec>
// <vc-code>
{
    if m == 0 {
        c
    } else if m >= c.len() {
        let mut v = Vec::<f64>::new();
        v.push(0.0);
        v
    } else {
        let mut v = Vec::<f64>::new();
        let mut i: usize = m;
        while i < c.len()
            invariant m <= i && i <= c.len() && v.len() == i - m
            decreases c.len() - i
        {
            v.push(c[i]);
            i += 1;
        }
        v
    }
}
// </vc-code>

}
fn main() {}