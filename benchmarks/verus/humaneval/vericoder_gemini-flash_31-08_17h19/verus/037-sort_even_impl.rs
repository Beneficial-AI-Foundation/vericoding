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
use vstd::seq_lib::*;

// Lemma to prove the effect of updating a sequence on its count
proof fn lemma_update_effect_on_count<T>(s: Seq<T>, i: int, v: T, x: T)
    requires
        0 <= i < s.len(),
    ensures
        count(s.update(i, v), x) == if v == x && s[i] != x {
            count(s, x) + 1
        } else if v != x && s[i] == x {
            count(s, x) - 1
        } else {
            count(s, x)
        },
{
    if s[i] == x {
        if v == x {
            // Case 1: s[i] == x and v == x. Count should be unchanged.
            assert(s.update(i, v) == s); // Because s[i] == v, update(i,v) is identity.
            assert(count(s.update(i, v), x) == count(s, x));
        } else {
            // Case 2: s[i] == x and v != x. Count should decrease by 1.
            assert(count(s.update(i, v), x) == count(s, x) - 1) by {
                assert(s.update(i,v).subsequence(0,i) == s.subsequence(0,i));
                assert(s.update(i,v).subsequence(i+1,s.len()) == s.subsequence(i+1,s.len()));
                assert(count(s.update(i, v), x) == count(s.subsequence(0,i), x) + count(s.subsequence(i+1, s.len()), x));
                assert(count(s, x) == count(s.subsequence(0,i), x) + 1 + count(s.subsequence(i+1, s.len()), x));
            }
        }
    } else { // s[i] != x
        if v == x {
            // Case 3: s[i] != x and v == x. Count should increase by 1.
            assert(count(s.update(i, v), x) == count(s, x) + 1) by {
                assert(s.update(i,v).subsequence(0,i) == s.subsequence(0,i));
                assert(s.update(i,v).subsequence(i+1,s.len()) == s.subsequence(i+1,s.len()));
                assert(count(s.update(i, v), x) == count(s.subsequence(0,i), x) + 1 + count(s.subsequence(i+1, s.len()), x));
                assert(count(s, x) == count(s.subsequence(0,i), x) + count(s.subsequence(i+1, s.len()), x));
            }
        } else {
            // Case 4: s[i] != x and v != x. Count should be unchanged.
            assert(count(s.update(i, v), x) == count(s, x)) by {
                assert(s.update(i,v).subsequence(0,i) == s.subsequence(0,i));
                assert(s.update(i,v).subsequence(i+1,s.len()) == s.subsequence(i+1,s.len()));
                assert(count(s.update(i, v), x) == count(s.subsequence(0,i), x) + count(s.subsequence(i+1, s.len()), x));
                assert(count(s, x) == count(s.subsequence(0,i), x) + count(s.subsequence(i+1, s.len()), x));
            }
        }
    }
}

// Helper to prove permutes for swap
proof fn lemma_swap_permutes<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        permutes(s.update(i, s[j]).update(j, s[i]), s),
{
    let val_i = s[i];
    let val_j = s[j];
    let s_ij_valj = s.update(i, val_j);
    let s_ij_valj_ji_vali = s_ij_valj.update(j, val_i);

    assert forall|x: T| count(s_ij_valj_ji_vali, x) == count(s, x) by {
        lemma_update_effect_on_count(s, i, val_j, x);
        lemma_update_effect_on_count(s_ij_valj, j, val_i, x);
    }
}


// Helper to prove transitivity of permutes
proof fn permutes_transitivity<T>(s1: Seq<T>, s2: Seq<T>, s3: Seq<T>)
    requires
        permutes(s1, s2),
        permutes(s2, s3),
    ensures
        permutes(s1, s3),
{
    assert forall|x: T| count(s1, x) == count(s3, x) by {
        assert(count(s1, x) == count(s2, x));
        assert(count(s2, x) == count(s3, x));
    }
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
    let mut result = l;
    let n = result.len();

    // Bubble sort-like approach for even indices
    // Iterate through even indices, performing passes
    // In each pass, bubble the largest even-indexed element to its correct sorted position
    // among even-indexed elements.
    if n == 0 {
        return result;
    }
    
    proof {
        seq_ext_implies_equal_len(result@, l@);
        assert(permutes(result@, l@)); // Initially, result is a permutation of l
    }

    let mut i = 0;
    while (i as int) < n
        invariant
            0 <= i as int <= n,
            // elements at odd indices remain unchanged
            forall|idx: int| 0 <= idx < n && idx % 2 == 1 ==> result[idx as int] == l[idx as int],
            permutes(result@, l@),
            result.len() == n,
            // The last 'i' even-indexed elements are sorted among themselves and are greater than or equal to any preceding even-indexed element.
            // 'boundary_idx_val' represents the largest index that is *not yet* sorted.
            // Any even_idx k such that k > boundary_idx_val and k % 2 == 0 is in its final sorted position.
            forall|k: int, m: int|
                #![trigger result[k]]
                #![trigger result[m]]
                let boundary_idx_val: int = n - (i as int) - 1;
                0 <= k < n && k % 2 == 0 && k > boundary_idx_val
                && 0 <= m < n && m % 2 == 0 && m < k
                ==> result[m] <= result[k],
    {
        // One pass of bubble sort on even elements
        let mut j = 0;
        while (j as int) < (n - (i as int) - 1)
            invariant
                0 <= i as int <= n,
                0 <= j as int <= (n - (i as int) - 1),
                // elements at odd indices remain unchanged
                forall|idx: int| 0 <= idx < n && idx % 2 == 1 ==> result[idx as int] == l[idx as int],
                permutes(result@, l@),
                result.len() == n,
                // The elements from `(n - (i as int) - 1)` to the end (at even indices) are sorted
                // and greater than or equal to any preceding even-indexed element.
                forall|k_outer: int, m_outer: int|
                    #![trigger result[k_outer]]
                    #![trigger result[m_outer]]
                    let boundary_idx_val: int = n - (i as int) - 1;
                    0 <= k_outer < n && k_outer % 2 == 0 && k_outer > boundary_idx_val
                    && 0 <= m_outer < n && m_outer % 2 == 0 && m_outer < k_outer
                    ==> result[m_outer] <= result[k_outer],
                // Within the current pass, the largest even element found so far in [0, j]
                // is at the last even position up to j.
                forall|k_inner: int, m_inner: int|
                    #![trigger result[k_inner]]
                    #![trigger result[m_inner]]
                    0 <= k_inner < n && k_inner % 2 == 0 && k_inner <= j as int
                    && 0 <= m_inner < n && m_inner % 2 == 0 && m_inner < k_inner
                    ==> result[m_inner] <= result[k_inner],
        {
            let current_idx = j;
            let next_idx = j + 1;

            if current_idx as int + 1 < n {
                if current_idx % 2 == 0 && next_idx % 2 == 0 {
                    // Both current_idx and next_idx are even
                    if result[current_idx as int] > result[next_idx as int] {
                        let pre_result_seq = result@; // Capture prior state for proof
                        let temp = result[current_idx as int];
                        result.set(current_idx as int, result[next_idx as int]);
                        result.set(next_idx as int, temp);

                        proof {
                            assert(result.len() == n);
                            // Permutes property preserved after swap
                            lemma_swap_permutes(pre_result_seq, current_idx as int, next_idx as int);
                            permutes_transitivity(result@, pre_result_seq, l@);
                        }
                    }
                } else if current_idx % 2 == 0 && next_idx % 2 != 0 {
                    // current_idx is even, next_idx is odd. Skip comparison for this pair.
                }

                // If current_idx is odd, we skip this comparison too.
            }
            j = j + 1;

            proof {
                // Ensure odd indices remain unchanged during the inner loop
                forall|idx: int| 0 <= idx < n && idx % 2 == 1 ==> {
                    assert(result[idx as int] == l[idx as int]);
                }
            }
        }
        i = i + 1;

        proof {
            // After the inner loop, confirm the sortedness of the last 'i' even elements:
            let boundary_idx_val = n - (i as int) - 1;
            assert(forall|k_outer: int, m_outer: int|
                 0 <= k_outer < n && k_outer % 2 == 0 && k_outer > boundary_idx_val
                 && 0 <= m_outer < n && m_outer % 2 == 0 && m_outer < k_outer
                 ==> result[m_outer] <= result[k_outer]);
        }
    }

    // Final checks for postconditions
    proof {
        assert(result.len() == l.len());
        assert(permutes(result@, l@));
        assert forall|i: int| 0 <= i < l.len() && i % 2 == 1 ==> result[i] == l[i] by {
            // Already proven by loop invariant
        }
        assert forall|i: int, j: int|
            0 <= i < j < l.len() && i % 2 == 0 && j % 2 == 0 ==> result[i] <= result[j] by {
                // When the outer loop terminates, `i` effectively becomes `n`.
                // This makes the `boundary_idx_val` in the outer loop invariant become `n - n - 1 = -1`.
                let final_boundary_idx: int = n - (n as int) - 1; // This will be -1
                // The outer loop invariant at termination with i=n implies:
                assert(forall|k: int, m: int|
                    0 <= k < n && k % 2 == 0 && k > final_boundary_idx
                    && 0 <= m < n && m % 2 == 0 && m < k
                    ==> result[m] <= result[k]);
                // This directly proves the final sortedness of even indexed elements for i, j.
            }
    }
    result
}
// </vc-code>

fn main() {}
}