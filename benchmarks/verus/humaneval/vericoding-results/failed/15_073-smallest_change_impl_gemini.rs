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
/* helper modified by LLM (iteration 5): fixed compile error by removing call to non-existent lemma */
proof fn lemma_diff_take(s: Seq<(i32, i32)>, i: int)
    requires 0 <= i < s.len()
    ensures diff(s.take(i + 1)) == diff(s.take(i)) + if s[i].0 != s[i].1 { 1int } else { 0int }
{
    assert(s.take(i+1) == s.take(i).push(s[i]));
}

/* helper modified by LLM (iteration 5): no change */
proof fn lemma_zip_halves_index(v: Seq<i32>, i: int)
    requires 0 <= i < (v.len() / 2) as int
    ensures zip_halves(v)[i] == (v[i], v[v.len() - 1 - i])
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
/* code modified by LLM (iteration 5): no change, relying on fixed helper proofs */
{
    let mut i: usize = 0;
    let mut change: usize = 0;
    let len = v.len();
    while i < len / 2
        invariant
            len == v.len(),
            0 <= i && i <= len / 2,
            change <= i,
            change as int == diff(zip_halves(v@).take(i as int)),
        decreases (len / 2) - i
    {
        let old_i = i;

        let a = v[i];
        let b = v[len - 1 - i];

        if a != b {
            change = change + 1;
        }
        i = i + 1;

        proof {
            let zh = zip_halves(v@);
            lemma_zip_halves_index(v@, old_i as int);
            lemma_diff_take(zh, old_i as int);
        }
    }
    change
}
// </vc-code>

}
fn main() {}