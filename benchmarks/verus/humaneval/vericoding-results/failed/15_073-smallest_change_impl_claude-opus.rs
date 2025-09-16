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
{
    /* code modified by LLM (iteration 5): Fixed loop invariant to handle count increment correctly */
    let n = v.len();
    let mut count: usize = 0;
    let half = n / 2;
    
    let mut i: usize = 0;
    while i < half
        invariant
            i <= half,
            half == n / 2,
            n == v.len(),
            half <= n,
            i <= n,
            n >= 1 ==> n - 1 - i < n,
            count <= half,
            forall |k: int| 0 <= k < i ==> {
                let pair = zip_halves(v@)[k];
                let j = n - 1 - k;
                (v@[k] != v@[j as int]) == (pair.0 != pair.1)
            },
            count == diff(zip_halves(v@).take(i as int)),
        decreases half - i
    {
        let j = n - 1 - i;
        if v[i] != v[j] {
            count = count + 1;
        }
        
        assert(zip_halves(v@).take((i + 1) as int) == zip_halves(v@).take(i as int).push(zip_halves(v@)[i as int]));
        i = i + 1;
    }
    
    assert(half as int == zip_halves(v@).len());
    assert(zip_halves(v@).take(half as int) == zip_halves(v@));
    
    count
}
// </vc-code>

}
fn main() {}