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

// </vc-helpers>

// <vc-spec>
fn smallest_change(v: Vec<i32>) -> (change: usize)

    requires
        v@.len() < usize::MAX,

    ensures
        change == diff(zip_halves(v@)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): changed change to nat and fixed assignment to avoid += */
{
    let n = v.len();
    let mut change: nat = 0;
    let mut i = 0;
    
    while i < n / 2
        invariant
            i <= n / 2,
            n == v@.len(),
            change == diff(zip_halves(v@).take(i as int)),
            change <= i as int,
        decreases (n / 2) - i,
    {
        let left_index = i;
        let right_index = n - 1 - i;
        
        if v[left_index] != v[right_index] {
            change = change + 1;
        }
        
        i += 1;
    }
    
    change as usize
}
// </vc-code>

}
fn main() {}