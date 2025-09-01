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
spec fn seq_even(s: Seq<i32>) -> Seq<i32> {
    if s.len() == 0 {
        Seq::empty()
    } else if s.len() == 1 {
        Seq::unit(s[0])
    } else {
        Seq::cons(s[0], seq_even(s.skip(2)))
    }
}

spec fn count_even_prefix(s: Seq<i32>, i: int, x: i32) -> int {
    if i == 0 {
        0
    } else {
        let prev = count_even_prefix(s, i - 1, x);
        prev + if (i - 1) % 2 == 0 && s[i - 1] == x { 1 } else { 0 }
    }
}

// Use the previously-declared lemma to prove the effect of an update on count
proof fn inner_expr_update_count_proof<T>(s: Seq<T>, i: int, v: T, x: T)
    requires 0 <= i < s.len()
    ensures count(s.update(i, v), x) == if v == x && s[i] != x {
        count(s, x) + 1
    } else if v != x && s[i] == x {
        count(s, x) - 1
    } else {
        count(s, x)
    }
{
    // The lemma `inner_expr_lemma_update_effect_on_count` is defined in the preamble.
    // We can apply it directly here.
    assert(inner_expr_lemma_update_effect_on_count(s, i, v, x));
}

// Prove that swapping two distinct positions preserves multiset (counts)
proof fn swap_preserves_count<T>(s: Seq<T>, i: int, j: int)
    requires 0 <= i < s.len()
    requires 0 <= j < s.len()
    requires i != j
    ensures forall|x: T| count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x)
{
    // Let s1 = s.update(i, s[j]); s2 = s1.update(j, s[i]);
    // We'll show for arbitrary x that count(s2, x) == count(s, x) by cases on equality with s[i] and s[j].
    proof {
        forall|x: T| {
            // Apply effect of first update
            assert(inner_expr_lemma_update_effect_on_count(s, i, s[j], x));
            let c_after_first =
                if s[j] == x && s[i] != x {
                    count(s, x) + 1
                } else if s[j] != x && s[i] == x {
                    count(s, x) - 1
                } else {
                    count(s, x)
                };
            assert(count(s.update(i, s[j]), x) == c_after_first);

            // s1[j] == s[j] because i != j
            assert(s.update(i, s[j])[j] == s[j]);

            // Apply effect of second update on s1
            assert(inner_expr_lemma_update_effect_on_count(s.update(i, s[j]), j, s[i], x));
            let c_after_second =
                if s[i] == x && s.update(i, s[j])[j] != x {
                    count(s.update(i, s[j]), x) + 1
                } else if s[i] != x && s.update(i, s[j])[j] == x {
                    count(s.update(i, s[j]), x) - 1
                } else {
                    count(s.update(i, s[j]), x)
                };
            assert(count(s.update(i, s[j]).update(j, s[i]), x) == c_after_second);

            // Now reason by cases on whether x equals s[i] and/or s[j]
            if x == s[i] {
                if x == s[j] {
                    // both equal -> no net change
                    assert(c_after_first == count(s, x));
                    assert(c_after_second == count(s, x));
                } else {
                    // x == s[i] && x != s[j]
                    // first update decreased by 1, second increased by 1 -> back to original
                    assert(c_after_first == count(s, x) - 1);
                    // s.update(i, s[j])[j] == s[j] != x
                    assert(s.update(i, s[j])[j] != x);
                    assert(c_after_second == (count(s, x) - 1) + 1);
                }
            } else {
                if x == s[j] {
                    // x != s[i] && x == s[j]
                    // first update increased by 1, second decreased by 1 -> back
                    assert(c_after_first == count(s, x) + 1);
                    // s.update(i, s[j])[j] == s[j] == x
                    assert(s.update(i, s[j])[j] == x);
                    assert(c_after_second == (count(s, x) + 1) - 1);
                } else {
                    // x != s[i] && x != s[j] -> unchanged both times
                    assert(c_after_first == count(s, x));
                    assert(c_after_second == count(s, x));
                }
            }

            // Conclude equality
            assert(count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x));
        }
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
    // Implementation: extract even-indexed elements, selection-sort them, write back.
    // We'll maintain and prove that the multiset of even elements is preserved while sorting,
    // and that odd positions remain unchanged.

    let mut r = l.clone();

    // Collect even-indexed elements into vals
    let mut vals: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < r.len()
        invariant 0 <= idx <= r.len()
        decreases r.len() - idx
    {
        if idx % 2 == 0 {
            vals.push(r[idx]);
        }
        idx = idx + 1;
    }

    // Remember the initial sequence of even elements as a spec-level snapshot
    let initial_vals_seq: Seq<i32> = vals@;

    // Selection sort on vals (in-place), while preserving multiset of vals
    let n: usize = vals.len();
    let mut i: usize = 0;
    while i < n
        invariant 0 <= i <= n,
                  // prefix 0..i is sorted
                  forall|p: int, q: int|
                      0 <= p < q < i as int ==> vals[p as usize] <= vals[q as usize],
                  // multiset preserved relative to initial_vals_seq
                  forall|x: i32| count(vals@, x) == count(initial_vals_seq, x)
        decreases n - i
    {
        // find index of minimum element in vals[i..n)
        let mut m: usize = i;
        let mut j: usize = i + 1;
        while j < n
            invariant i <= m < n,
                      i <= j <= n,
                      // m is index of a minimal element among vals[i..j)
                      forall|k: int| i as int <= k < j as int ==> vals[m] <= vals[k as usize],
                      // multiset preserved
                      forall|x: i32| count(vals@, x) == count(initial_vals_seq, x)
            decreases n - j
        {
            if vals[j] < vals[m] {
                m = j;
            }
            j = j + 1;
        }

        // swap vals[i] and vals[m] if different
        if i != m {
            // perform swap with explicit set operations to make sequence updates visible
            let vi = vals[i];
            let vm = vals[m];
            vals.set(i, vm);
            vals.set(m, vi);

            // Now prove swapping preserves multiset of vals
            // Use swap_preserves_count on the seq-level view
            proof {
                swap_preserves_count(vals@, i as int, m as int);
            }
        }

        i = i + 1;
    }

    // Now write back sorted even elements into r at even indices
    let mut p: usize = 0;
    while p < n
        invariant 0 <= p <= n,
                  // positions for k < p have been written back: r[2*k] == vals[k]
                  forall|k: int| 0 <= k < p as int ==> r[2 * (k as usize)] == vals[k as usize],
                  // odd positions unchanged so far (all odd positions are unchanged globally; we will assert at end)
                  forall|k: int| 0 <= k < r.len() as int && k % 2 == 1 ==> r[k as usize] == l[k as usize]
        decreases n - p
    {
        // write vals[p] into r at index 2*p
        let write_idx = 2 * p;
        r.set(write_idx, vals[p]);
        p = p + 1;
    }

    // Proofs of postconditions

    // 1) length preserved
    assert(r.len() == l.len());

    // 2) odd positions unchanged: we never modified odd indices of r (we only set even indices), so they equal l
    proof {
        forall|i: int| 0 <= i < r.len() && i % 2 == 1 ==> {
            assert(r[i as usize] == l[i as usize]);
        }
    }

    // 3) even positions sorted: for any even indices i<j, r[i] <= r[j]
    proof {
        // Let k = i/2, p = j/2, then 0 <= k < p < n and vals[k] <= vals[p] by selection sort invariant
        forall|i: int, j: int|
            0 <= i < j < r.len()
// </vc-code>

fn main() {}
}