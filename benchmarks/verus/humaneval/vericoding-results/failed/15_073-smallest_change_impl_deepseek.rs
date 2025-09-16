// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn zip_halves<T>(v: Seq<T>) -> (ret: Seq<(T, T)>) {
    v.take((v.len() / 2) as int).zip_with(v.skip(((v.len() + 1) / 2) as int).reverse())
}

spec fn diff(s: Seq<(i32, i32)>) -> (ret: int) {
    s.fold_left(
        0,
        |acc: int, x: (i32, i32)|
            if (x.0 != x.1) {
                acc + 1
            } else {
                acc
            },
    )
}
// </vc-preamble>

// <vc-helpers>
proof fn len_div2_proof(n: int) 
    ensures 
        (n / 2) as nat + ((n + 1) / 2) as nat == n,
{
    /* helper modified by LLM (iteration 5): Fixed nat conversion */
    assert((n / 2) as nat <= n);
    assert(((n + 1) / 2) as nat <= n);
}
// </vc-helpers>

// <vc-spec>
fn smallest_change(v: Vec<i32>) -> (change: usize)

    requires
        v@.len() < usize::MAX,

    ensures
        change == diff(zip_halves(v@)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed integer casting */
    let half = (v.len() / 2) as usize;
    let mut change: usize = 0;
    
    let mut i: usize = 0;
    while i < half
        invariant
            i <= half,
            change as int == diff(zip_halves(v@.take(i as int))),
            v@.len() - i >= half,
        decreases half - i
    {
        let j = v.len() - 1 - i;
        if v[i] != v[j] {
            change = change + 1;
        }
        i = i + 1;
    }
    
    change
}
// </vc-code>

}
fn main() {}