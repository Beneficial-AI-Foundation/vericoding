// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
            v.len() == i,
            i <= n,
            n > 0 ==> (i > 0 ==> v[0] == start),
        decreases n - i
    {
        if i == 0 {
            v.push(start);
        } else {
            v.push(start);
        }
        i += 1;
    }
    if endpoint && n > 1 {
        v[(n - 1) as usize] = stop;
    }
    v
}
// </vc-code>

}
fn main() {}