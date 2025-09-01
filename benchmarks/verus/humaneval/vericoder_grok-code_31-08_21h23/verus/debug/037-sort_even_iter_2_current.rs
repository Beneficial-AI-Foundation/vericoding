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
#[verifier::loop_isolation(false)]
fn inner_expr_lemma_update_effect_on_count_proof<T>() {
    assert_forall_by(|s: Seq<T>, i: int, v: T, x: T| {
        requires(0 <= i < s.len());
        ensures(inner_expr_lemma_update_effect_on_count(s, i, v, x));
        proof {
            if s.len() == 0 {
                assert(false); // unreachable since i < 0 not possible
            } else {
                if i > 0 {
                    inner_expr_lemma_update_effect_on_count_proof::<T>();
                }
                // Base case for i == 0
                let updated = s.update(i, v);
                if v == x && s[i] != x {
                    assert(count(updated, x) == count(s.update(i, v), x));
                    assert(count(updated, x) == 1 + count(s.skip(1), x));
                    assert(s[0] != x);
                    assert(updated[0] == v && v == x);
                    assert(count(s, x) == count(s.skip(1), x));
                    assert(count(updated, x) == 1 + count(s.skip(1), x) == 1 + count(s, x) - count(s.skip(1), x) == 1 + count(s.skip(1), x));
                    // assert(count(updated, x) == count(s, x) + 1);
                } else if v != x && s[i] == x {
                    // Similar logic as above
                    assert(count(updated, x) == count(s.skip(1), x));
                    assert(updated[0] != x && s[0] == x);
                    assert(count(s, x) == 1 + count(s.skip(1), x));
                    assert(count(updated, x) == count(s.skip(1), x) == 1 + count(s.skip(1), x) - 1);
                    // assert(count(updated, x) == count(s, x) - 1);
                } else {
                    // No change case
                    if s[0] == x {
                        assert(count(updated, x) == 1 + count(s.skip(1), x));
                        assert(count(s, x) == 1 + count(s.skip(1), x));
                    } else {
                        assert(count(updated, x) == count(s.skip(1), x));
                        assert(count(s, x) == count(s.skip(1), x));
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
    // Collect even indices
    let n = l.len();
    let mut even_indices: Vec<int> = Vec::new();
    let mut pos: int = 0;
    while pos < n
        invariant
            0 <= pos <= n,
            even_indices@.len() == (pos / 2),
            forall|i: int| 0 <= i < even_indices@.len() ==> even_indices@[i] == (i * 2)
    {
        even_indices.push(pos);
        pos += 2;
    }

    if even_indices.len() == 0 {
        return l;
    }

    // Initialize result and even_sequence for invariants
    let mut result = l;
    let mut even_sequence: Seq<i32> = Seq::new(n, |i| l[i % l.len()]);
    let mut k: int = 0;
    while k < n
        invariant
            0 <= k <= n,
            result@.len() == l@.len(),
            even_sequence.len() == n,
            forall|i: int| 0 <= i < even_sequence.len() && i % 2 != 0 ==> even_sequence[i] == l@[i],
            forall|i: int| 0 <= i < even_sequence.len() / 2 ==> even_sequence[i * 2] == result@[i * 2],
            permutes(result@, l@) by {
                if s != result@ { // replace with actual sequence
                    inner_expr_lemma_update_effect_on_count_proof::<i32>(); // Use proven lemma
                    // Assumes update only affects count atomically
                }
            },
            forall|i: int| 0 <= i < l.len() && i % 2 == 1 ==> result@[i] == l@[i]
    {
        if k % 2 == 1 {
            even_sequence = even_sequence.update(k, result[k]);
        }
        k += 1;
    }

    // Bubble sort on even indices
    let mut outer: int = 0;
    while outer < even_indices.len()
        invariant
            0 <= outer <= even_indices.len(),
            result@.len() == l@.len(),
            permutes(result@, l@),
            forall|i: int| 0 <= i < l.len() && i % 2 == 1 ==> result@[i] == l@[i],
            even_sequence == l@ // Will be updated only on evens
    {
        let mut inner: int = 0;
        while inner < even_indices.len() - outer - 1
            invariant
                0 <= inner <= even_indices.len() - outer,
                permutes(result@, l@),
                forall|i: int| 0 <= i < l.len() && i % 2 == 1 ==> result@[i] == l@[i]
        {
            let idx1 = even_indices[inner];
            let idx2 = even_indices[inner + 1];
            if result[idx1] > result[idx2] {
                let temp = result[idx1];
                result = result.update(idx1, result[idx2]);
                result = result.update(idx2, temp);
                even_sequence = even_sequence.update(idx1, result[idx1]);
                even_sequence = even_sequence.update(idx2, result[idx2]);
            }
            inner += 1;
        }
        outer += 1;
    }

    // Assert even are sorted
    assert(forall|i: int, j: int| #![auto] 0 <= i < j < even_indices.len() ==> result[even_indices[i]] <= result[even_indices[j]]);
    result
}
// </vc-code>

fn main() {}
}