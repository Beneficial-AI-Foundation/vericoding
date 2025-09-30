// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n_a: int, n_b: int, k: int, m: int, a: Seq<int>, b: Seq<int>) -> bool {
    n_a >= 1 && n_b >= 1 &&
    k >= 1 && k <= n_a &&
    m >= 1 && m <= n_b &&
    a.len() == n_a &&
    b.len() == n_b
}

spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> #[trigger] s.index(i) <= #[trigger] s.index(j)
}

spec fn valid_selection(a: Seq<int>, b: Seq<int>, k: int, m: int) -> bool
    recommends k >= 1 && k <= a.len() && m >= 1 && m <= b.len()
{
    a[k - 1] < b[b.len() - m]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): lemmas relating map from i8 to int for index and length */
proof fn lemma_map_index_i8_to_int(s: Seq<i8>, i: int)
    requires
        0 <= i,
        i < s.len(),
    ensures
        s.map(|j, x: i8| x as int).index(i) == s.index(i) as int,
{
    assert(s.map(|j, x: i8| x as int).index(i) == s.index(i) as int);
}

/* helper modified by LLM (iteration 2): lemma that mapping preserves length */
proof fn lemma_map_len_i8_to_int(s: Seq<i8>)
    ensures
        s.map(|j, x: i8| x as int).len() == s.len(),
{
    assert(s.map(|j, x: i8| x as int).len() == s.len());
}
// </vc-helpers>

// <vc-spec>
fn solve(n_a: i8, n_b: i8, k: i8, m: i8, a: Vec<i8>, b: Vec<i8>) -> (result: &'static str)
    requires 
        valid_input(n_a as int, n_b as int, k as int, m as int, a@.map(|i, x: i8| x as int), b@.map(|i, x: i8| x as int)),
        is_sorted(a@.map(|i, x: i8| x as int)),
        is_sorted(b@.map(|i, x: i8| x as int))
    ensures 
        result == "YES" || result == "NO",
        result == "YES" <==> valid_selection(a@.map(|i, x: i8| x as int), b@.map(|i, x: i8| x as int), k as int, m as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute indices with usize only, prove bounds and equivalence to spec, then compare */
    let a_len: usize = a.len();
    let b_len: usize = b.len();

    let k_usize: usize = k as usize;
    let m_usize: usize = m as usize;

    proof {
        assert(a@.len() == a_len as int);
        assert(b@.len() == b_len as int);
        assert(1 <= k as int && k as int <= a_len as int);
        assert(1 <= m as int && m as int <= b_len as int);
    }

    assert(k_usize >= 1usize);
    assert(k_usize <= a_len);
    assert(m_usize >= 1usize);
    assert(m_usize <= b_len);

    let k_idx: usize = k_usize - 1usize;
    let b_idx: usize = b_len - m_usize;

    let ak_i8: i8 = a[k_idx];
    let bb_i8: i8 = b[b_idx];

    let ans = if ak_i8 < bb_i8 { "YES" } else { "NO" };

    proof {
        let k_i: int = k as int;
        let m_i: int = m as int;
        let k_idx_i: int = k_i - 1;
        let b_idx_i: int = b_len as int - m_i;

        assert(0 <= k_idx_i && k_idx_i < a@.len());
        assert(0 <= b_idx_i && b_idx_i < b@.len());

        assert(a@[k_idx_i] == ak_i8);
        assert(b@[b_idx_i] == bb_i8);

        lemma_map_index_i8_to_int(a@, k_idx_i);
        lemma_map_index_i8_to_int(b@, b_idx_i);

        let ak_int: int = ak_i8 as int;
        let bb_int: int = bb_i8 as int;

        assert(a@.map(|j, x: i8| x as int)[k_idx_i] == ak_int);
        assert(b@.map(|j, x: i8| x as int)[b_idx_i] == bb_int);

        assert(valid_selection(a@.map(|j, x: i8| x as int), b@.map(|j, x: i8| x as int), k_i, m_i)
               == (ak_int < bb_int));

        if ak_i8 < bb_i8 { assert(ans == "YES"); } else { assert(ans == "NO"); }
        assert(ans == "YES" <==> valid_selection(a@.map(|j, x: i8| x as int), b@.map(|j, x: i8| x as int), k_i, m_i));
    }

    ans
}
// </vc-code>


}

fn main() {}