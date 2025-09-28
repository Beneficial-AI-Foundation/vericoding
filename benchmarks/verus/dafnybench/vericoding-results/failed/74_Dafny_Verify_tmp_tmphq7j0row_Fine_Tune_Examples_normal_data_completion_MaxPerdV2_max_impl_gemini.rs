// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn contains(v: i32, a: Seq<i32>, n: int) -> bool {
    exists|j: int| 0 <= j < n && a[j] == v
}

spec fn upper_bound(v: i32, a: Seq<i32>, n: int) -> bool {
    forall|j: int| 0 <= j < n ==> a[j] <= v
}

spec fn is_max(m: i32, a: Seq<i32>, n: int) -> bool {
    contains(m, a, n) && upper_bound(m, a, n)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Replaced `implies` with `ensures` in `forall` proof statements to fix compilation error. */
proof fn max_inductive_lem(m: i32, s: Seq<i32>, v: i32)
    requires is_max(m, s, s.len())
    ensures is_max(if v > m { v } else { m }, s.push(v), s.len() + 1)
{
    let new_s = s.push(v);
    let new_len = s.len() + 1;
    let new_m = if v > m { v } else { m };

    if v > m {
        assert(new_s.last() == v);
        assert(contains(v, new_s, new_len));

        assert(upper_bound(m, s, s.len()));
        forall|j: int| 0 <= j < new_len ensures new_s[j] <= v {
            if j < s.len() {
                assert(s[j] <= m && m < v);
                assert(new_s[j] <= v);
            } else {
                assert(new_s[j] == v);
            }
        }
        assert(upper_bound(v, new_s, new_len));
    } else {
        assert(contains(m, s, s.len()));
        let j = choose|k: int| 0 <= k < s.len() && s[k] == m;
        assert(new_s[j] == m);
        assert(contains(m, new_s, new_len));

        assert(upper_bound(m, s, s.len()));
        forall|j: int| 0 <= j < new_len ensures new_s[j] <= m {
            if j < s.len() {
                assert(new_s[j] <= m);
            } else {
                assert(new_s[j] == v);
                assert(v <= m);
            }
        }
        assert(upper_bound(m, new_s, new_len));
    }
}
// </vc-helpers>

// <vc-spec>
fn max(a: &[i32], n: usize) -> (result: i32)
    requires 0 < n <= a.len(),
    ensures is_max(result, a@, n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Confirmed loop logic is sound and relies on the now-fixed `max_inductive_lem`. */
    let mut m = a[0];
    let mut i: usize = 1;

    while i < n
        invariant
            0 < i <= n,
            n <= a.len(),
            is_max(m, a@.subrange(0, i as int), i as int),
        decreases n - i
    {
        let s_i = a@.subrange(0, i as int);
        let v = a[i];

        proof {
            let s_i_plus_1 = a@.subrange(0, (i + 1) as int);
            assert_seqs_equal!(s_i_plus_1, s_i.push(v));
            max_inductive_lem(m, s_i, v);
        }

        if v > m {
            m = v;
        }
        i = i + 1;
    }
    m
}
// </vc-code>

}
fn main() {}