// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn geomspace(start: f64, stop: f64, n: usize, endpoint: bool) -> (result: Vec<f64>)
    requires 
        start != 0.0,
        stop != 0.0,
        n > 0,
    ensures
        result.len() == n,
        n > 0 ==> result[0] == start,
        (endpoint && n > 1) ==> result[(n - 1) as int] == stop,
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            v.len() == i,
        decreases (n - i) as int
    {
        v.push(0.0);
        i += 1;
    }
    v[0] = start;
    if endpoint && n > 1 {
        v[n - 1] = stop;
    }
    v
}
// </vc-code>

}
fn main() {}