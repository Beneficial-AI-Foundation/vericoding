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
spec fn compute_diff<T>(v: &Vec<T>, i: usize, n: usize) -> (ret: usize)
    recommends
        i <= n / 2,
    decreases n - i,
{
    if i == n / 2 {
        0
    } else {
        let diff = if v[i] != v[n - 1 - i] { 1 } else { 0 };
        diff + compute_diff(v, i + 1, n)
    }
}

#[verifier::proof]
proof fn lemma_compute_diff_equals_diff<T>(v: &Vec<T>, i: usize, n: usize)
    requires
        v@.len() == n as int,
        v@.len() < usize::MAX,
    ensures
        i == 0 ==> compute_diff(v, i, n) == diff(zip_halves(v@)),
    decreases n - i,
{
    if i == n / 2 {
    } else {
        let z = zip_halves(v@);
        let m = n / 2;
        if i < m {
            lemma_compute_diff_equals_diff(v, i + 1, n);
            assert(z[i as int].0 == v@[i as int]);
            assert(z[i as int].1 == v@[n as int - 1 - i as int]);
            assert(compute_diff(v, i, n) == (if v[i] != v[n - 1 - i] { 1 } else { 0 }) + compute_diff(v, i + 1, n));
            assert(diff(z.take((m - i) as int)) == compute_diff(v, i, n));
            // folding diff over the full z
        }
    }
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
    let n_usize = v.len();
    let m_usize = n_usize / 2;
    let n_int = v@.len();
    let m_int = n_int / 2;
    let mut count = 0;
    let mut i = 0;
    let ghost_z = zip_halves(v@);
    proof {
        assert(v@.len() == n_int as usize);
        assert(m_int == m_usize as int);
        assert(forall |k: int| 0 <= k < i ==> ghost_z[k].0 == v@[k] && ghost_z[k].1 == v@[n_int - 1 - k]);  // establish for i=0
        assert(count + compute_diff(&v, 0, n_usize) == compute_diff(&v, 0, n_usize));
        // other initial assertions
    }
    while i < m_usize 
        invariant({
            0 <= i && i <= m_usize,
            count + compute_diff(&v, i, n_usize) == compute_diff(&v, 0, n_usize),
            ghost_z.len() == m_int,
            forall |k: int| 0 <= k < i as int ==> ghost_z[k].0 == v@[k] && ghost_z[k].1 == v@[n_int - 1 - k],
        })
    {
        if v[i] != v[n_usize - 1 - i] {
            count += 1;
            proof {
                assert(ghost_z[i as int].0 != ghost_z[i as int].1);
                assert(i as int < m_int);
            }
        }
        i += 1;
    }
    proof {
        lemma_compute_diff_equals_diff(&v, 0, n_usize);
        assert(count == diff(ghost_z));
    }
    count
}
// </vc-code>

fn main() {}
}