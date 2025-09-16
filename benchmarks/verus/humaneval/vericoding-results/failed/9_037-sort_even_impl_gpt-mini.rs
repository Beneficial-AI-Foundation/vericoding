// <vc-preamble>
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

spec fn permutes<T>(s1: Seq<T>, s2: Seq<T>) -> (result:bool) {
    forall|x: T| count(s1, x) == count(s2, x)
}

spec fn inner_expr_lemma_update_effect_on_count<T>(s: Seq<T>, i: int, v: T, x: T) -> (result:bool) {
    count(s.update(i, v), x) == if v == x && s[i] != x {
        count(s, x) + 1
    } else if v != x && s[i] == x {
        count(s, x) - 1
    } else {
        count(s, x)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): transitivity of permutes */
proof fn permutes_transitive<T>(a: Seq<T>, b: Seq<T>, c: Seq<T>)
    requires
        permutes(a, b),
        permutes(b, c),
    ensures
        permutes(a, c),
{
    proof {
        forall|x: T| {
            assert(count(a, x) == count(b, x));
            assert(count(b, x) == count(c, x));
            assert(count(a, x) == count(c, x));
        };
    }
}

/* helper modified by LLM (iteration 5): swapping two positions preserves multiset counts */
proof fn swap_preserves_permutes<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        permutes(s.update(i, s[j]).update(j, s[i]), s),
{
    proof {
        if i == j {
            assert(s.update(i, s[j]).update(j, s[i]) == s);
            assert(permutes(s.update(i, s[j]).update(j, s[i]), s));
        } else {
            forall|x: T| {
                assert(inner_expr_lemma_update_effect_on_count(s, i, s[j], x));
                assert(inner_expr_lemma_update_effect_on_count(s.update(i, s[j]), j, s[i], x));
                assert(count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x));
            };
        }
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn sort_even(l: Vec<i32>) -> (result: Vec<i32>)

    ensures
        l.len() == result.len(),
        permutes(result@, l@),
        forall|i: int| 0 <= i < l.len() && i % 2 == 1 ==> result[i] == l[i],
        forall|i: int, j: int|
            #![auto]
            0 <= i < j < l.len() && i % 2 == 0 && j % 2 == 0 ==> result[i] <= result[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): selection-sort-style swaps on even indices, preserving permutation and odd-index invariants */
    let n_usize: usize = l.len();
    let mut res = l.clone();

    proof {
        assert(res@ == l@);
        assert(permutes(res@, l@));
        let n: int = n_usize as int;
        assert(forall|k: int| 0 <= k < n && k % 2 == 1 ==> res@[k] == l@[k]);
    }

    let mut iu: usize = 0usize;
    while iu < n_usize
        invariant
            0 <= iu as int,
            iu as int <= n_usize as int,
            permutes(res@, l@),
            forall|k: int| 0 <= k < n_usize as int && k % 2 == 1 ==> res@[k] == l@[k],
        decreases (n_usize as int) - (iu as int)
    {
        let mut ju: usize = iu + 2usize;
        while ju < n_usize
            invariant
                iu + 2usize <= ju,
                ju <= n_usize,
                permutes(res@, l@),
                forall|k: int| 0 <= k < n_usize as int && k % 2 == 1 ==> res@[k] == l@[k],
            decreases (n_usize as int) - (ju as int)
        {
            if res[iu] > res[ju] {
                let seq_old = res@;
                res.swap(iu, ju);
                proof {
                    let ii: int = iu as int;
                    let jj: int = ju as int;
                    swap_preserves_permutes::<i32>(seq_old, ii, jj);
                    permutes_transitive::<i32>(res@, seq_old, l@);
                    assert(iu % 2usize == 0usize);
                    assert(ju % 2usize == 0usize);
                    assert(forall|k: int| 0 <= k < n_usize as int && k % 2 == 1 ==> res@[k] == l@[k]);
                }
            }
            ju = ju + 2usize;
        }
        iu = iu + 2usize;
    }

    res
}

// </vc-code>

}
fn main() {}