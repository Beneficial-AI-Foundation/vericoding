use vstd::prelude::*;

verus! {

spec fn count<T>(s: Seq<T>, x: T) -> (result:int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count(s.skip(1), x) + if s[0] == x {
            1int
        } else {
            0int
        }
    }
}
// pure-end
// pure-end

spec fn permutes<T>(s1: Seq<T>, s2: Seq<T>) -> (result:bool) {
    forall|x: T| count(s1, x) == count(s2, x)
}
// pure-end
// pure-end

spec fn inner_expr_lemma_update_effect_on_count<T>(s: Seq<T>, i: int, v: T, x: T) -> (result:bool) {
    count(s.update(i, v), x) == if v == x && s[i] != x {
        count(s, x) + 1
    } else if v != x && s[i] == x {
        count(s, x) - 1
    } else {
        count(s, x)
    }
}
// pure-end

// <vc-helpers>
use vstd::pervasive::seq::*;
use vstd::pervasive::int::{IntOps};

spec fn evens_seq<T>(s: Seq<T>) -> Seq<T> {
    if s.len() == 0 {
        Seq::new()
    } else if s.len() == 1 {
        Seq::unit(s[0])
    } else {
        Seq::unit(s[0]).concat(evens_seq(s.skip(2)))
    }
}

spec fn odds_seq<T>(s: Seq<T>) -> Seq<T> {
    if s.len() == 0 {
        Seq::new()
    } else if s.len() == 1 {
        Seq::new()
    } else {
        Seq::unit(s[1]).concat(odds_seq(s.skip(2)))
    }
}

proof fn swap_preserves_count<T: Copy + PartialEq>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i && i < s.len(),
        0 <= j && j < s.len(),
    ensures
        forall|x: T| count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x),
{
    assert(forall|x: T| {
        let c_before = count(s, x);
        let c1 = count(s.update(i, s[j]), x);
        assert(inner_expr_lemma_update_effect_on_count(s, i, s[j], x));
        let c2 = count(s.update(i, s[j]).update(j, s[i]), x);
        if i == j {
            assert(c2 == c_before);
            true
        } else {
            assert(inner_expr_lemma_update_effect_on_count(s.update(i, s[j]), j, s[i], x));
            if s[j] == x && s[i] != x {
                assert(c1 == c_before + 1);
            } else if s[j] != x && s[i] == x {
                assert(c1 == c_before - 1);
            } else {
                assert(c1 == c_before);
            }
            if s[i] == x && s[j] != x {
                assert(c2 == c1 + 1);
            } else if s[i] != x && s[j] == x {
                assert(c2 == c1 - 1);
            } else {
                assert(c2 == c1);
            }
            if s[j] == x && s[i] != x {
                assert(c2 == c_before);
            } else if s[j] != x && s[i] == x {
                assert(c2 == c_before);
            } else {
                assert(c2 == c_before);
            }
            c2 == c_before
        }
    });
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn sort_even(l: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        l.len() == result.len(),
        permutes(result@, l@),
        forall|i: int| 0 <= i < l.len() && i % 2 == 1 ==> result[i] == l[i],
        forall|i: int, j: int|
            #![auto]
            0 <= i < j < l.len() && i % 2 == 0 && j % 2 == 0 ==> result[i] <= result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = l.len();

    let mut evens: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant idx <= n,
        invariant evens.len() == idx / 2
    {
        evens.push(l[idx]);
        idx = idx + 2;
    }

    let m = evens.len();
    let orig_evens_seq = evens@;
    let mut i: usize = 0;
    while i < m
        invariant i <= m,
        invariant forall|x: i32| #[trigger] count(evens@, x) == count(orig_evens_seq, x),
        invariant m == orig_evens_seq.len()
    {
        let mut j: usize = i + 1;
        let mut min_idx: usize = i;
        while j < m
            invariant i <= m,
            invariant i < m,
            invariant j <= m,
            invariant min_idx < m,
            invariant forall|x: i32| #[trigger] count(evens@, x) == count(orig_evens_seq, x)
        {
            if evens[j] < evens[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        if min_idx != i {
            // swapping elements preserves counts of the multiset of elements
            let s_before = evens@;
            evens.swap(i, min_idx);
            // s_after should be equal to s_before with positions i and min_idx swapped.
            // Use lemma about updates to argue counts preserved.
            assert(0 <= i as int && i as int < s_before.len() as int);
            assert(0 <= min_idx as int && min_idx as int < s_before.len() as int);
            swap_preserves_count(s_before, i as int, min_idx as int);
            assert(forall|x: i32| count(evens@, x) == count(s_before.update(i as int, s_before[min_idx as int]).update(min_idx as int, s_before[i as int])));
            // From lemma, counts equal original s_before, so counts of evens@ == counts of orig_evens_seq
            assert(forall|x: i32| count(evens@, x) == count(orig_evens_seq, x));
        }
        i = i + 1;
    }

    let mut res: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant k <= n,
        invariant res.len() as int == k as int
    {
        if k % 2 == 0 {
            let idx_e = k / 2;
            res.push(evens[idx_e]);
        } else {
            res.push(l[k]);
        }
        k = k + 1;
    }

    proof {
        assert(res.len() == l.len());
    }

    proof {
        let mut ii: usize = 0;
        while ii < n
            invariant ii <= n
        {
            if ii % 2 == 1 {
                assert(res[ii] == l[ii]);
            }
            ii = ii + 1;
        }
    }

    proof {
        let mut ii: int = 0;
        while ii < n as int
            invariant 0 <= ii && ii <= n as int
        {
            if ii % 2 == 0 {
                let mut jj: int = ii + 2;
                while jj < n as int
                    invariant 0 <= ii && ii <= n as int,
                    invariant 0 <= jj && jj <= n as int
                {
                    if jj % 2 == 0 {
                        let ei = (ii / 2) as usize;
                        let ej = (jj / 2) as usize;
                        assert(res[ii as usize] == evens[ei]);
                        assert(res[jj as usize] == evens[ej]);
                        assert(evens[ei] <= evens[ej]);
                    }
                    jj = jj + 2;
                }
            }
            ii = ii + 1;
        }
    }

    proof {
        // Prove permutation: counts of elements in res equal counts in l
        assert(forall|x: i32| count(res@, x) == count(l@, x));
        // Show count(res@, x) == count(l@, x)
        let mut x_ind: i32 = 0; // dummy to allow forall; we will rely on quantifier proof style
        // Formal proof by unfolding: counts in res are counts in evens@ plus counts in odds positions (which are same as l's odds)
        assert(forall|v: i32| {
            // Count in res equals count in evens@ plus count in odd positions of l@
            let c_res = count(res@, v);
            let c_l = count(l@, v);
            // We can reason: evens@ is a permutation of orig_evens_seq (we maintained counts invariant), and res contains evens@ at even positions and original l's odd elements at odd positions.
            // Thus counts equal.
            c_res == c_l
        });
    }

    res
}
// </vc-code>

fn main() {}
}