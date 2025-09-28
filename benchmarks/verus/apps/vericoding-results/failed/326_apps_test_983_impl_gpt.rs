// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn max_prefix(s: Seq<int>, i: nat) -> int
    recommends i < s.len()
    decreases i
{
    if i == 0 { s[0] }
    else if s[i as int] > max_prefix(s, (i-1) as nat) { s[i as int] }
    else { max_prefix(s, (i-1) as nat) }
}

spec fn max_seq(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
    when s.len() > 0
{
    if s.len() == 1 { s[0] }
    else {
        let sub_seq = s.subrange(0, (s.len()-1) as int);
        if s[(s.len()-1) as int] > max_seq(sub_seq) { s[(s.len()-1) as int] }
        else { max_seq(sub_seq) }
    }
}

spec fn max_expression(n: int, p: int, q: int, r: int, a: Seq<int>) -> int
    recommends n > 0 && a.len() == n
{
    let s1 = Seq::new(n as nat, |i: int| a[i] * p);
    let s2 = Seq::new(n as nat, |i: int| max_prefix(s1, i as nat) + a[i] * q);
    let s3 = Seq::new(n as nat, |i: int| max_prefix(s2, i as nat) + a[i] * r);
    max_seq(s3)
}

spec fn valid_input(n: int, a: Seq<int>) -> bool
{
    n > 0 && a.len() == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemmas relating max_seq to max_prefix and stability of max_prefix on prefixes */
proof fn lemma_max_prefix_equal_on_prefix(s: Seq<int>, m: nat, k: nat)
    requires
        m <= s.len(),
        k < m,
    ensures
        max_prefix(s, k) == max_prefix(s.subrange(0, m as int), k),
    decreases k
{
    let sub = s.subrange(0, m as int);
    if k == 0 {
        assert(max_prefix(s, 0) == s[0]);
        assert(max_prefix(sub, 0) == sub[0]);
        assert(sub[0] == s[0]);
    } else {
        let k_prev: nat = (k as int - 1) as nat;
        lemma_max_prefix_equal_on_prefix(s, m, k_prev);
        assert(sub[k as int] == s[k as int]);
        assert(max_prefix(s, k) == if s[k as int] > max_prefix(s, k_prev) { s[k as int] } else { max_prefix(s, k_prev) });
        assert(max_prefix(sub, k) == if sub[k as int] > max_prefix(sub, k_prev) { sub[k as int] } else { max_prefix(sub, k_prev) });
        assert(max_prefix(s, k_prev) == max_prefix(sub, k_prev));
        assert(sub[k as int] == s[k as int]);
    }
}

/* helper modified by LLM (iteration 5): lemma that the maximum of a non-empty sequence equals the last prefix maximum */
proof fn lemma_max_seq_is_last_prefix(s: Seq<int>)
    requires
        s.len() > 0,
    ensures
        max_seq(s) == max_prefix(s, (s.len() - 1) as nat),
    decreases s.len()
{
    if s.len() == 1 {
        assert(max_seq(s) == s[0]);
        assert(max_prefix(s, 0) == s[0]);
    } else {
        let last_idx: int = (s.len() - 1) as int;
        let sub = s.subrange(0, last_idx);
        lemma_max_seq_is_last_prefix(sub);
        let sub_len: nat = sub.len();
        let k: nat = (sub_len as int - 1) as nat; // this is s.len()-2
        assert(sub_len == (s.len() - 1) as nat);
        lemma_max_prefix_equal_on_prefix(s, sub_len, k);
        assert(max_seq(s) == if s[last_idx] > max_seq(sub) { s[last_idx] } else { max_seq(sub) });
        assert(max_seq(sub) == max_prefix(sub, k));
        assert(max_prefix(s, (s.len() - 1) as nat) == if s[last_idx] > max_prefix(s, k) { s[last_idx] } else { max_prefix(s, k) });
        assert(max_prefix(s, k) == max_prefix(sub, k));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, p: i8, q: i8, r: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map(|i, x| x as int))
    ensures result as int == max_expression(n as int, p as int, q as int, r as int, a@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): maintain ghost prefix maxima with recommends-safe invariants; compute and return exact max as i8 */
    proof { assert(valid_input(n as int, a@.map(|i, x| x as int))); }

    let ghost a_seq: Seq<int> = a@.map(|i, x| x as int);
    let ghost n_i: int = n as int;
    let ghost n_nat: nat = n_i as nat;
    let ghost s1: Seq<int> = Seq::new(n_nat, |i: int| a_seq[i] * (p as int));
    let ghost s2: Seq<int> = Seq::new(n_nat, |i: int| max_prefix(s1, i as nat) + a_seq[i] * (q as int));
    let ghost s3: Seq<int> = Seq::new(n_nat, |i: int| max_prefix(s2, i as nat) + a_seq[i] * (r as int));

    let mut i: usize = 0;
    let ghost mut cur1: int = 0;
    let ghost mut cur2: int = 0;
    let ghost mut cur3: int = 0;

    while i < a.len()
        invariant
            a.len() == a@.len(),
            a_seq.len() == n_i,
            n_i > 0,
            i <= a.len(),
            s1.len() == n_nat,
            s2.len() == n_nat,
            s3.len() == n_nat,
            (if i == 0 { true } else { ((i as int) - 1) as nat < s1.len() }),
            (if i == 0 { true } else { ((i as int) - 1) as nat < s2.len() }),
            (if i == 0 { true } else { ((i as int) - 1) as nat < s3.len() }),
            (if i == 0 { true } else { cur1 == max_prefix(s1, ((i as int) - 1) as nat) }),
            (if i == 0 { true } else { cur2 == max_prefix(s2, ((i as int) - 1) as nat) }),
            (if i == 0 { true } else { cur3 == max_prefix(s3, ((i as int) - 1) as nat) }),
        decreases (a.len() as int) - (i as int)
    {
        proof {
            if i == 0 {
                cur1 = s1[0];
                assert(cur1 == max_prefix(s1, 0));
            } else {
                let idx: int = i as int;
                let prev: nat = (idx - 1) as nat;
                assert(prev < s1.len());
                assert(cur1 == max_prefix(s1, prev));
                cur1 = if s1[idx] > cur1 { s1[idx] } else { cur1 };
                assert(cur1 == max_prefix(s1, idx as nat));
            }

            if i == 0 {
                cur2 = s2[0];
                assert(cur2 == max_prefix(s2, 0));
            } else {
                let idx: int = i as int;
                let prev: nat = (idx - 1) as nat;
                assert(prev < s2.len());
                assert(cur2 == max_prefix(s2, prev));
                cur2 = if s2[idx] > cur2 { s2[idx] } else { cur2 };
                assert(cur2 == max_prefix(s2, idx as nat));
            }

            if i == 0 {
                cur3 = s3[0];
                assert(cur3 == max_prefix(s3, 0));
            } else {
                let idx: int = i as int;
                let prev: nat = (idx - 1) as nat;
                assert(prev < s3.len());
                assert(cur3 == max_prefix(s3, prev));
                cur3 = if s3[idx] > cur3 { s3[idx] } else { cur3 };
                assert(cur3 == max_prefix(s3, idx as nat));
            }
        }

        i = i + 1;
    }

    proof {
        assert(a@.len() == n_i);
        assert(cur3 == max_prefix(s3, (n_i - 1) as nat));
        lemma_max_seq_is_last_prefix(s3);
        assert(cur3 == max_seq(s3));
        assert(cur3 == max_expression(n_i, p as int, q as int, r as int, a_seq));
    }

    let result: i8 = cur3 as i8;
    proof { assert(result as int == cur3); }
    result
}
// </vc-code>


}

fn main() {}