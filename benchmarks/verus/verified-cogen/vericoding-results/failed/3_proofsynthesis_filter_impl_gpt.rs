// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
spec fn div3(x: u64) -> bool { x % 3 == 0 }
// </vc-helpers>

// <vc-spec>
fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)

    requires 
        old(y).len() == 0,

    ensures 
        y@ == x@.filter(|k:u64| k%3 == 0),
// </vc-spec>
// <vc-code>
{
    let n = x.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == x.len(),
            y@ == x@.take(i as int),
        decreases n - i
    {
        let xi = x[i];
        y.push(xi);
        i += 1;
    }
    y.retain(|v: &u64| (*v) % 3 == 0);
}
// </vc-code>

}
fn main() {}