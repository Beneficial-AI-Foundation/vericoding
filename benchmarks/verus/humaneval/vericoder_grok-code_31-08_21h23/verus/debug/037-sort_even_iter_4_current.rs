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
#[verifier.external]
assume_specification::<alloc::slice::<i32>::sort>(
    |s: &mut [i32]| { s.sort(); },
    |pre, post| ensures post.s@ == old(pre.s@).sort()
);

#[verifier::loop_isolation(false)]
fn inner_expr_lemma_update_effect_on_count_proof<T>() {
    assert_forall_by(|s: Seq<T>, i: int, v: T, x: T| {
        requires(0 <= i < s.len());
        ensures(inner_expr_lemma_update_effect_on_count(s, i, v, x));
        proof {
            if s.len() == 0 {
                assert(false);
            } else {
                if i > 0 {
                    inner_expr_lemma_update_effect_on_count_proof::<T>();
                }
                let updated = s.update(i, v);
                let cnt_updated = count(updated, x);
                let cnt_s = count(s, x);
                if i == 0 {
                    if v == x && s[0] != x {
                        assert(cnt_updated == 1 + count(updated.skip(1), x));
                        assert(updated.skip(1) == s.skip(1));
                        assert(cnt_s == count(s.skip(1), x));
                        assert(cnt_updated == cnt_s + 1);
                    } else if v != x && s[0] == x {
                        assert(cnt_updated == count(updated.skip(1), x));
                        assert(updated.skip(1) == s.skip(1));
                        assert(cnt_s == 1 + count(s.skip(1), x));
                        assert(cnt_updated == cnt_s - 1);
                    } else {
                        assert(cnt_updated == cnt_s);
                    }
                } else {
                    if v == x && s[i] != x {
                        inner_expr_lemma_update_effect_on_count_proof::<T>();
                        let lemma_s_i = count(s.update(i, v), x) == count(s, x) + 1;
                        assert(cnt_updated == 1 + count(updated.skip(1), x));
                        assert(true);
                    } else if v != x && s[i] == x {
                        inner_expr_lemma_update_effect_on_count_proof::<T>();
                        let lemma_s_i = count(s.update(i, v), x) == count(s, x) - 1;
                        assert(true);
                    } else {
                        inner_expr_lemma_update_effect_on_count_proof::<T>();
                        let lemma_s_i = count(s.update(i, v), x) == count(s, x);
                        assert(true);
                    }
                }
            }
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
    let mut even_vals: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            even_vals@.len() == (i / 2),
            forall|j: int| 0 <= j < even_vals@.len() ==> even_vals@[j] == l@[(j * 2)]
    {
        if i % 2 == 0 {
            even_vals.push(l[i]);
        }
        i += 1;
    }

    even_vals.sort();
    assert(forall|j: int, k: int| 0 <= j < k < even_vals.len() ==> even_vals[j] <= even_vals[k]);

    let mut result: Vec<i32> = Vec::new();
    let mut even_idx = 0;
    i = 0;
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            even_idx <= even_vals.len(),
            result@.len() == i,
            even_vals@.len() == ((l@.len() + 1) / 2),
            forall|j: int| 0 <= j < result@.len() && j % 2 == 1 ==> result@[j] == l@[j],
            forall|j: int| 0 <= j < result@.len() && j % 2 == 0 ==> result@[j] == even_vals@[j / 2],
            permutes(result@ + even_vals@.subrange(even_idx as int, even_vals@.len() as int), l@)
    {
        if i % 2 == 1 {
            result.push(l[i]);
        } else {
            result.push(even_vals[even_idx]);
            even_idx += 1;
        }
        i += 1;
    }
    assert(forall|j: int, k: int| 0 <= j < k < l.len() && j % 2 == 0 && k % 2 == 0 ==> result[j] <= result[k]);
    result
}
// </vc-code>

fn main() {}
}