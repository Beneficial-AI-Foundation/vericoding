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
    assert(true); // trivial to enter proof context
    fix |x: i32| {
        // apply update effect twice using the provided spec lemma
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

        // simplify c2 using knowledge s.update(i,s[j])[j] == s[j]
        if s[i] == x && s[j] != x {
            // c1 was count(s,x) + 1; now since s[i]==x and s[j]!=x, c2 = c1 - 1 = count(s,x)
            assert(c1 == count(s, x) + 1);
            assert(c2 == c1 - 1);
            assert(c2 == count(s, x));
        } else if s[i] != x && s[j] == x {
            // c1 was count(s,x) - 1; now since s[i]!=x and s[j]==x, c2 = c1 + 1 = count(s,x)
            assert(c1 == count(s, x) - 1);
            assert(c2 == c1 + 1);
            assert(c2 == count(s, x));
        } else {
            // either both equal or both not equal: c1 == count(s,x) and c2 == c1
            assert(c1 == count(s, x));
            assert(c2 == c1);
            assert(c2 == count(s, x));
        }

        // conclude
        assert(count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x));
    }
}

proof fn swap_seq_perm(s: Seq<i32>, i: int, j: int)
    requires 0 <= i < s.len(),
    requires 0 <= j < s.len(),
    requires i != j,
    ensures permutes(s.update(i, s[j]).update(j, s[i]), s),
{
    // permutes is defined by equality of counts for all x
    assert(forall|x: i32| count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x));
    // The previous assertion follows from swap_seq_preserves_count
    swap_seq_preserves_count(s, i, j);
}

proof fn permutes_trans(a: Seq<i32>, b: Seq<i32>, c: Seq<i32>)
    requires permutes(a, b),
    requires permutes(b, c),
    ensures permutes(a, c),
{
    // For all x, count(a,x) == count(b,x) and count(b,x) == count(c,x) hence count(a,x) == count(c,x)
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
            invariant j % 2 == 0 || (j == i + 1), // j steps by 2; allow j==i+1 when n small
            invariant permutes(l@, orig@),
            invariant forall|k: int| 0 <= k < n && k % 2 == 1 ==> l[k] == orig[k],
            invariant forall|a: int, b: int|
                0 <= a < b < n && a % 2 == 0 && b % 2 == 0 && b < i ==> l[a] <= l[b],
        {
            // compare elements at even indices i and j
            if j < n {
                let vi = l.get(i as usize);
                let vj = l.get(j as usize);
                if vi > vj {
                    // perform swap by doing two sets, capturing old sequence for reasoning
                    let old = l.clone();
                    let old_seq: Seq<i32> = old@;
                    // set i to vj and j to vi
                    l.set(i as usize, old.get(j as usize));
                    l.set(j as usize, old.get(i as usize));

                    // After these two sets, l@ == old_seq.update(i, old_seq[j]).update(j, old_seq[i])
                    proof {
                        // show permutation preserved: swap_seq_perm on old_seq then trans with existing permutes
                        swap_seq_perm(old_seq, i, j);
                        // old was equal to old w.r.t orig by invariant permutes(old@, orig@)
                        // but we need to use that before the swap, permutes(old@, orig@) held
                        // Use invariant: permutes(old@, orig@) because old == pre-swap l
                        // Combine permutations: permutes(l@, old@) (from swap) and permutes(old@, orig@) (invariant) => permutes(l@, orig@)
                        // First, from swap_seq_perm we have permutes(old_seq.update(i, old_seq[j]).update(j, old_seq[i]), old_seq).
                        // And l@ equals that updated sequence, so permutes(l@, old@) holds.
                        // l@ equals old_seq.update(i, old_seq[j]).update(j, old_seq[i]) by semantics of set operations.
                        assert(l@ == old_seq.update(i, old_seq[j]).update(j, old_seq[i]));
                        // From swap_seq_perm: permutes(old_seq.update(...), old_seq)
                        swap_seq_perm(old_seq, i, j);
                        // From invariant we know permutes(old@, orig@)
                        assert(permutes(old@, orig@));
                        // Now combine: permutes(l@, old@) and permutes(old@, orig@) => permutes(l@, orig@)
                        permutes_trans(l@, old@, orig@);
                    }
                    // also odd indices unchanged: since i and j are even, odd k not equal i or j
                    proof {
                        let old_seq: Seq<i32> = old@;
                        // For any odd k, if k != i and k != j then old_seq.update(i, old_seq[j]).update(j, old_seq[i])[k] == old_seq[k]
                        // And since l@ equals that updated seq, equality holds with orig via invariant
                        // We can show directly:
                        assert(forall|k: int| 0 <= k < n && k % 2 == 1 ==> l[k] == orig[k]);
                    }
                }
            }
            j = j + 2;
        }
        i = i + 2;
    }

    // At loop exit, even indices should be sorted by the invariant
    // Return the sorted vector
    l
    // impl-end
}
// </vc-code>

fn main() {}
}