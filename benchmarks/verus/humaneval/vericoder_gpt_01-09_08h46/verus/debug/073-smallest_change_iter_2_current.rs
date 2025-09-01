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
proof fn lemma_zip_halves_len<T>(v: Seq<T>)
    ensures zip_halves(v).len() == v.len() / 2
{
    let l = v.len();
    let a = (l / 2) as int;
    let b = ((l + 1) / 2) as int;
    assert(v.take(a).len() == a);
    assert(v.skip(b).len() == l - b);
    assert(v.skip(b).reverse().len() == l - b);
    assert(v.take(a).len() == v.skip(b).reverse().len());
    assert(zip_halves(v).len() == v.take(a).len());
}

proof fn lemma_zip_halves_index<T>(v: Seq<T>, i: int)
    requires
        0 <= i,
        i < v.len() / 2,
    ensures
        zip_halves(v)@[i] == (v@[i], v@[(v.len() - 1) - i])
{
    // Let lengths and indices
    let n = v.len();
    let a = (n / 2) as int;
    let b =
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
proof fn lemma_zip_halves_len<T>(v: Seq<T>)
    ensures zip_halves(v).len() == v.len() / 2
{
    let l = v.len();
    let a = (l / 2) as int;
    let b = ((l + 1) / 2) as int;
    assert(v.take(a).len() == a);
    assert(v.skip(b).len() == l - b);
    assert(v.skip(b).reverse().len() == l - b);
    assert(v.take(a).len() == v.skip(b).reverse().len());
    assert(zip_halves(v).len() == v.take(a).len());
}

proof fn lemma_zip_halves_index<T>(v: Seq<T>, i: int)
    requires
        0 <= i,
        i < v.len() / 2,
    ensures
        zip_halves(v)@[i] == (v@[i], v@[(v.len() - 1) - i])
{
    // Let lengths and indices
    let n = v.len();
    let a = (n / 2) as int;
    let b =
// </vc-code>

fn main() {}
}