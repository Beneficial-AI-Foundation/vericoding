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
spec fn seq_len<T>(s: Seq<T>) -> int {
    s.len()
}

proof fn seq_update_unchanged(s: Seq<i32>, i: int, v: i32, k: int)
    requires 0 <= i < s.len(),
    requires 0 <= k < s.len(),
    ensures k != i ==> s.update(i, v)[k] == s[k],
{
    if k != i {
        // by definition of update, indexes different remain same
        assert(s.update(i, v)[k] == s[k]);
    } else {
        // nothing to prove when k == i
    }
}

proof fn swap_seq_preserves_count(s: Seq<i32>, i: int, j: int)
    requires 0 <= i < s.len(),
    requires 0 <= j < s.len(),
    requires i != j,
    ensures forall|x: i32| count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x),
{
    // fix arbitrary x
    assert(true);
    fix |x: i32| {
        assert(inner_expr_lemma_update_effect_on_count(s, i, s[j], x));
        let c1 = if s[j] == x && s[i] != x {
            count(s, x) + 1
        } else if s[j] != x && s[i] == x {
            count(s, x) - 1
        } else {
            count(s, x)
        };
        assert(count(s.update(i, s[j]), x) == c1);

        // Since i != j, the first update did not change index j, so s.update(i, s[j])[j] == s[j]
        assert(s.update(i, s[j])[j] == s[j]);

        assert(inner_expr_lemma_update_effect_on_count(s.update(i, s[j]), j, s[i], x));
        let c2 = if s[i] == x && s.update(i, s[j])[j] != x {
            count(s.update(i, s[j]), x) + 1
        } else if s[i] != x && s.update(i, s[j])[j] == x {
            count(s.update(i, s[j]), x) - 1
        } else {
            count(s.update(i, s[j]), x)
        };
        assert(count(s.update(i, s[j]).update(j, s[i]), x) == c2);

        if s[i] == x && s[j] != x {
            assert(c1 == count(s, x) + 1);
            assert(c2 == c1 - 1);
            assert(c2 == count(s, x));
        } else if s[i] != x && s[j] == x {
            assert(c1 == count(s, x) - 1);
            assert(c2 == c1 + 1);
            assert(c2 == count(s, x));
        } else {
            assert(c1 == count(s, x));
            assert(c2 == c1);
            assert(c2 == count(s, x));
        }

        assert(count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x));
    }
}

proof fn swap_seq_perm(s: Seq<i32>, i: int, j: int)
    requires 0 <= i < s.len(),
    requires 0 <= j < s.len(),
    requires i != j,
    ensures permutes(s.update(i, s[j]).update(j, s[i]), s),
{
    assert(forall|x: i32| count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x));
    swap_seq_preserves_count(s, i, j);
}

proof fn permutes_trans(a: Seq<i32>, b: Seq<i32>, c: Seq<i32>)
    requires permutes(a, b),
    requires permutes(b, c),
    ensures permutes(a, c),
{
    assert(forall|x: i32| count(a, x) == count(c, x));
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
    // impl-start
    let n: int = l.len() as int;
    let orig = l.clone(); // save original for specifications

    let mut i: int = 0;
    while i < n
        invariant 0 <= i <= n,
        invariant i % 2 == 0,
        invariant permutes(l@, orig@),
        invariant forall|k: int| 0 <= k < n && k % 2 == 1 ==> l[k] == orig[k],
        invariant forall|a: int, b: int|
            0 <= a < b < n && a % 2 == 0 && b % 2 == 0 && b < i ==> l[a] <= l[b],
    {
        let mut j: int = i + 2;
        while j < n
            invariant 0 <= i <= n,
            invariant 0 <= j <= n,
            invariant i % 2 == 0,
            invariant j % 2 == 0 || (j == i + 1),
            invariant permutes(l@, orig@),
            invariant forall|k: int| 0 <= k < n && k % 2 == 1 ==> l[k] == orig[k],
            invariant forall|a: int, b: int|
                0 <= a < b < n && a % 2 == 0 && b % 2 == 0 && b < i ==> l[a] <= l[b],
        {
            if j < n {
                let vi = l.get(i as usize);
                let vj = l.get(j as usize);
                if vi > vj {
                    // capture sequence before mutation
                    let old_seq: Seq<i32> = l@;

                    // perform swap using values from old_seq
                    l.set(i as usize, old_seq[j]);
                    l.set(j as usize, old_seq[i]);

                    // prove that l@ equals the sequence obtained by two updates of old_seq
                    proof {
                        assert(l@ == old_seq.update(i, old_seq[j]).update(j, old_seq[i]));
                        // from swap_seq_perm we have permutes(updated, old_seq)
                        swap_seq_perm(old_seq, i, j);
                        // from the invariant before mutation we have permutes(old_seq, orig@)
                        assert(permutes(old_seq, orig@));
                        // combine to get permutes(l@, orig@)
                        permutes_trans(l@, old_seq, orig@);
                    }

                    // odd indices unchanged: show for all odd k, l[k] == orig[k]
                    proof {
                        fix |k: int| {
                            if 0 <= k && k < n && k % 2 == 1 {
                                // l@ == old_seq.update(i, old_seq[j]).update(j, old_seq[i])
                                // since k is odd and i,j are even, k != i and k != j
                                // apply seq_update_unchanged for the second update (index j)
                                assert(old_seq.update(i, old_seq[j]).update(j, old_seq[i])[k] == old_seq.update(i, old_seq[j])[k]);
                                // apply seq_update_unchanged for the first update (index i)
                                assert(old_seq.update(i, old_seq[j])[k] == old_seq[k]);
                                // therefore l[k] == old_seq[k]
                                assert(l[k] == old_seq[k]);
                                // and by invariant old_seq[k] == orig[k]
                                assert(old_seq[k] == orig[k]);
                                assert(l[k] == orig[k]);
                            } else {
                                // nothing to prove
                            }
                        }
                    }
                }
            }
            j = j + 2;
        }
        i = i + 2;
    }

    l
    // impl-end
}
// </vc-code>

fn main() {}
}