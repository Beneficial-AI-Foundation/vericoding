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
proof lemma_count_update_eq<T>(s: Seq<T>, i: int, v: T, x: T)
    requires
        0 <= i < s.len(),
    ensures
        count(s.update(i, v), x) == if v == x && s[i] != x {
            count(s, x) + 1
        } else if v != x && s[i] == x {
            count(s, x) - 1
        } else {
            count(s, x)
        }
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        if i == 0 {
            if v == x {
                if s[0] == x {
                } else {
                }
            } else {
                if s[0] == x {
                } else {
                }
            }
        } else {
            lemma_count_update_eq(s.skip(1), i - 1, v, x);
        }
    }
}

proof lemma_permutes_update<T>(s1: Seq<T>, s2: Seq<T>, i: int, v: T)
    requires
        permutes(s1, s2),
        0 <= i < s1.len(),
    ensures
        permutes(s1.update(i, v), s2.update(i, v)),
{
    assert forall|x: T| count(s1.update(i, v), x) == count(s2.update(i, v), x) by {
        lemma_count_update_eq(s1, i, v, x);
        lemma_count_update_eq(s2, i, v, x);
    };
}

proof lemma_permutes_transitive<T>(s1: Seq<T>, s2: Seq<T>, s3: Seq<T>)
    requires
        permutes(s1, s2),
        permutes(s2, s3),
    ensures
        permutes(s1, s3),
{
    assert forall|x: T| count(s1, x) == count(s3, x) by {
        assert(count(s1, x) == count(s2, x));
        assert(count(s2, x) == count(s3, x));
    };
}

spec fn is_even_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() && i % 2 == 0 && j % 2 == 0 ==> s[i] <= s[j]
}

spec fn odd_indices_unchanged(s1: Seq<i32>, s2: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < s1.len() && i % 2 == 1 ==> s2[i] == s1[i]
}

proof lemma_bubble_sort_preserves_odd_indices(s: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j < s.len(),
    ensures
        forall|k: int| 0 <= k < s.len() && k % 2 == 1 ==> s.update(i, s[j]).update(j, s[i])[k] == s[k],
{
    assert forall|k: int| 0 <= k < s.len() && k % 2 == 1 implies s.update(i, s[j]).update(j, s[i])[k] == s[k] by {
        if k == i {
            assert(s.update(i, s[j])[i] == s[j]);
            assert(s.update(i, s[j]).update(j, s[i])[i] == s.update(i, s[j])[i]);
        } else if k == j {
            assert(s.update(i, s[j])[j] == s[j]);
            assert(s.update(i, s[j]).update(j, s[i])[j] == s[i]);
        } else {
            assert(s.update(i, s[j])[k] == s[k]);
            assert(s.update(i, s[j]).update(j, s[i])[k] == s.update(i, s[j])[k]);
        }
    };
}

proof lemma_bubble_sort_preserves_perm(s: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j < s.len(),
    ensures
        permutes(s.update(i, s[j]).update(j, s[i]), s),
{
    assert forall|x: i32| count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x) by {
        lemma_count_update_eq(s, i, s[j], x);
        let s1 = s.update(i, s[j]);
        lemma_count_update_eq(s1, j, s[i], x);
    };
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
    let mut result = l.clone();
    let n = result.len() as int;
    
    proof {
        assert(permutes(result@, result@));
        assert(odd_indices_unchanged(result@, result@));
        assert(is_even_sorted(result@));
    }
    
    let mut i: int = 0;
    while i < n - 2
        invariant
            0 <= i <= n - 2,
            permutes(result@, l@),
            forall|k: int| 0 <= k < n && k % 2 == 1 ==> result@[k] == l@[k],
            forall|p: int, q: int| 0 <= p < q < i && p % 2 == 0 && q % 2 == 0 ==> result@[p] <= result@[q],
        decreases n - 2 - i,
    {
        let mut j: int = i + 2;
        while j < n
            invariant
                i <= j <= n,
                permutes(result@, l@),
                forall|k: int| 0 <= k < n && k % 2 == 1 ==> result@[k] == l@[k],
                forall|p: int, q: int| 0 <= p < q < i && p % 2 == 0 && q % 2 == 0 ==> result@[p] <= result@[q],
                forall|p: int| i <= p < j && p % 2 == 0 ==> result@[i] <= result@[p],
            decreases n - j,
        {
            if j % 2 == 0 && result@[i] > result@[j] {
                let temp = result[i as usize];
                result[i as usize] = result[j as usize];
                result[j as usize] = temp;
                
                proof {
                    let old_seq = result@;
                    let new_seq = old_seq.update(i, old_seq[j]).update(j, old_seq[i]);
                    lemma_bubble_sort_preserves_perm(old_seq, i, j);
                    lemma_bubble_sort_preserves_odd_indices(old_seq, i, j);
                    assert(permutes(new_seq, old_seq));
                    lemma_permutes_transitive(new_seq, old_seq, l@);
                }
            } else {
                proof {
                    assert(result@ == result@);
                }
            }
            j = j + 2;
        }
        i = i + 2;
    }
    
    result
}
// </vc-code>

fn main() {}
}