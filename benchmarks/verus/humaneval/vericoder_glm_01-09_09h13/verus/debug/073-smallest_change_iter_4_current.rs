use vstd::prelude::*;

verus! {

spec fn zip_halves<T>(v: Seq<T>) -> (ret: Seq<(T, T)>) {
    v.take((v.len() / 2) as int).zip_with(v.skip(((v.len() + 1) / 2) as int).reverse())
}
// pure-end
// pure-end

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
// pure-end

// <vc-helpers>
spec fn zip_halves_slice<T>(v: Seq<T>, start: int, end: int) -> (ret: Seq<(T, T)>)
    requires 0 <= start <= end <= v.len()
{
    v.take(end as int).skip(start as int).zip_with(
        v.take(v.len() - start as int).skip(v.len() - end as int).reverse()
    )
}

spec fn diff_slice(s: Seq<(i32, i32)>, start: int, end: int) -> (ret: int)
    requires 0 <= start <= end <= s.len()
{
    s.take(end as int).skip(start as int).fold_left(
        0,
        |acc: int, x: (i32, i32)|
            if (x.0 != x.1) {
                acc + 1
            } else {
                acc
            },
    )
}

proof fn diff_take lemma(s: Seq<(i32, i32)>, n: int)
    requires 0 <= n <= s.len()
    ensures diff(s.take(n)) == diff_slice(s, 0, n)
{
    reveal(diff);
    reveal(diff_slice);
}
// </vc-helpers>

// <vc-spec>
fn smallest_change(v: Vec<i32>) -> (change: usize)
    // pre-conditions-start
    requires
        v@.len() < usize::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        change == diff(zip_halves(v@)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = v.len();
    let half = n / 2;
    let mut count = 0;
    for i in 0..half
        invariant
            0 <= i <= half,
            if half > 0 {
                i < n && n - 1 - i >= half
            } else {
                true
            },
            count == diff(zip_halves(v@).take(i as int)),
    {
        if v@[i] != v@[n - 1 - i] {
            count += 1;
        }
    }
    count
}
// </vc-code>

fn main() {}
}