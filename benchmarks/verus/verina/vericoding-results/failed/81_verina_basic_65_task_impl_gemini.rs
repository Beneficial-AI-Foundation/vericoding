// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn square_root(n: usize) -> (result: usize)
    ensures
        result * result <= n,
        n < (result + 1) * (result + 1),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while (i + 1) * (i + 1) <= n
        invariant
            i * i <= n,
        decreases n - i,
    {
        i = i + 1;
    }
    i
}
// </vc-code>

}
fn main() {}