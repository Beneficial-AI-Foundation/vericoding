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
proof fn zip_halves_len<T>(v: Seq<T>)
    ensures
        zip_halves(v).len() == v.len() / 2,
{
}

proof fn zip_halves_index(v: Seq<i32>, i: int)
    requires
        0 <= i,
        i < zip_halves(v).len(),
    ensures
        zip_halves(v)[i] == (v[i], v[v.len() - 1 - i]),
{
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
    let n = v.len();
    let mut i: usize = 0;
    let mut count: usize = 0;

    while i < n / 2
        invariant
            i <= n / 2,
            count as int == diff(zip_halves(v@).take(i as int)),
        decreases (n / 2 - i) as int
    {
        let a = v[i];
        let b = v[n - 1 - i];
        if a != b {
            count += 1;
        }
        i += 1;
    }

    assert(i == n / 2);

    proof {
        let s = zip_halves(v@);
        assert(s.len() == (n / 2) as int) by { zip_halves_len::<i32>(v@); }
        assert(count as int == diff(s.take(i as int)));
        assert(i as int == s.len());
        assert(s.take(s.len()) == s);
    }

    count
}
// </vc-code>

}
fn main() {}