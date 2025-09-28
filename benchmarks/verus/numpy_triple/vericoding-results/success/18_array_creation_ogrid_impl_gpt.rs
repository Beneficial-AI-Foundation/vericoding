// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn id_usize(x: usize) -> (r: usize)
    ensures
        r == x,
{
    x
}
// </vc-helpers>

// <vc-spec>
fn ogrid(start: f32, stop: f32, n: usize) -> (result: Vec<f32>)
    requires n > 0,
    ensures 
        result.len() == n,
        (n == 1 ==> result[0] == start),
        (n > 1 ==> result[0] == start),
        (n > 1 ==> result[n - 1] == stop),
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<f32> = Vec::new();
    v.push(start);
    if n > 1 {
        let mut i: usize = 1;
        while i < n - 1
            invariant
                v.len() == i,
                i >= 1,
                i <= n - 1,
                v[0] == start,
            decreases (n - i) as int
        {
            v.push(start);
            assert(v[0] == start);
            i += 1;
        }
        v.push(stop);
    }
    v
}
// </vc-code>

}
fn main() {}