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
spec fn compute_diff(v: Seq<i32>) -> usize
    ensures
        compute_diff(v) == diff(zip_halves(v))
{
    let half_len = (v.len() / 2) as int;
    let first_half = v.take(half_len);
    let second_half = v.skip(((v.len() + 1) / 2) as int).reverse();
    let zipped = first_half.zip_with(second_half);
    zipped.fold_left(
        0,
        |acc: usize, x: (i32, i32)|
            if x.0 != x.1 {
                acc + 1
            } else {
                acc
            }
    )
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
    let mut change: usize = 0;
    let half_len: usize = v.len() / 2;
    let mut i: usize = 0;

    while i < half_len
        invariant
            half_len == v@.len() / 2,
            i <= half_len,
            change <= i,
            change == diff(zip_halves(v@).take(i as int)),
    {
        let first = v[i];
        let second = v[v.len() - 1 - i];
        if first != second {
            change = change + 1;
        }
        i = i + 1;
    }

    change
}
// </vc-code>

}
fn main() {}