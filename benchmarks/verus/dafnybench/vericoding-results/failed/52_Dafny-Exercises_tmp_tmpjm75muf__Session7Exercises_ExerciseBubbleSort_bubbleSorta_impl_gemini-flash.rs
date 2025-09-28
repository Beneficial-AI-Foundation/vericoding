use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<i32>, i: int, j: int) -> bool //j excluded
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
fn swap(a: &mut Vec<i32>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
    ensures
        a@.swap(i, j) == old(a)@,
        a.len() == old(a).len(),
{
    // Verus handles `Vec::swap` directly in proofs by recognizing the behavior of the `std::vec::Vec::swap` method.
    // The explicit Rust code for `swap` is actually `std::vec::Vec::swap`
    // However, for the purposes of a Verus problem, we provide a placeholder
    // acknowledging that it maps to the actual Rust swap.
    // Rust's `Vec::swap` method is `(a.as_mut_slice()).swap(i as usize, j as usize);`
    // but a manual swap here is also fine to ensure the `ensures` clause can be proven.
    let temp = a[i as usize];
    a[i as usize] = a[j as usize];
    a[j as usize] = temp;
}
// </vc-helpers>

// <vc-spec>
fn bubbleSorta(a: &mut Vec<i32>, c: usize, f: usize) //f excluded
    requires 
        c <= f,
        f <= old(a).len(), //when c==f empty sequence
    ensures 
        sorted_seg(a@, c as int, f as int),
        a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
        a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
        a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
// </vc-spec>
// <vc-code>
{
    let mut i = c;
    while i < f {
        invariant
            c <= i && i <= f,
            a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
            a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
            a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
            sorted_seg(a@, c as int, i as int),
        {
            let mut j = f - 1;
            while j > i {
                invariant
                    i <= j && j < f, // j must be at least i, and less than f (f is exclusive)
                    // The invariant for the inner loop: a[j] is the minimum of elements in a[j..f).
                    // This implies that after the loop, when j becomes i, a[i] will be the minimum of a[i..f).
                    forall|k: int| #[trigger] (i < k && k < f && k >= j) ==> a@[j] <= a@[k],
                    // Also, we need to preserve the sorting of the prefix that is already sorted.
                    // And the multiset equality. These are inherited from the outer loop invariant.
                    a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
                    a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
                    a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
                    sorted_seg(a@, c as int, i as int),
                {
                    if a@[(j - 1) as int] > a@[j as int] {
                        let pre_a = a@;
                        swap(a, (j - 1) as int, j as int);
                        proof {
                            assert(a@.swap(j-1, j) == pre_a);
                            // Prove sorted_seg(a@, c as int, i as int)
                            assert forall|l: int, k: int| (c <= l && l <= k && k < i) implies a@[l] <= a@[k] by {
                                // Since l, k < i, and i <= j-1, they are not affected by swap at j-1, j.
                                assert(l < j-1 || k < j-1 || l >= j+1); // at least one is true for the current swap indices
                                if (l < j-1 || l >= j+1 || k < j-1 || k >= j+1) {
                                    assert(a@[l] == pre_a@[l]);
                                    assert(a@[k] == pre_a@[k]);
                                } else if k == j-1 { // l < j-1 and k == j-1
                                    assert(l < j-1);
                                    assert(a@[l] == pre_a@[l]);
                                    assert(a@[j-1] == pre_a@[j]);
                                    if l < j-1 { // we need a@[l] <= a@[j-1]
                                        assert(pre_a@[l] <= pre_a@[j-1]); // From sorted_seg prior to swap
                                        assert(pre_a@[j] < pre_a@[j-1]); // From if condition
                                        assert(a@[j-1] == pre_a@[j]);
                                        assert(pre_a@[l] <= pre_a@[j]); // Since pre_a[j] is minimum of pre_a[j..f)
                                        assert(pre_a@[l] <= a@[j-1]);
                                    }
                                } else if l == j-1 && k == j { // This case does not apply for sorted_seg(...,i)
                                    // because l,k must be < i. But j always >= i+1. So j-1 >= i.
                                    // So this part (l,k < i) is unaffected by the swap, as swap always happens at or after i's position
                                    // j is always >= i+1, thus j-1 >= i. So the sorted_seg(c, i) is unchanged.
                                }
                            }
                            // Prove forall|k: int| (i < k && k < f && k >= j-1) ==> a@[j-1] <= a@[k]
                            assert forall|k: int| (i < k && k < f && k >= j-1) implies a@[j-1] <= a@[k] by {
                                let new_j_minus_1_val = pre_a@[j as int]; // This is the new value at j-1
                                // We need to show new_j_minus_1_val <= a@[k] for k in [j-1, f).
                                if k == (j - 1) as int {
                                    assert(new_j_minus_1_val <= a@[k]); // Trivial a <= a
                                } else if k == j as int {
                                    // new_j_minus_1_val <= a@[j] means pre_a@[j] <= pre_a@[j-1]. This is true by 'if' condition.
                                    assert(new_j_minus_1_val <= a@[j]);
                                } else { // k > j
                                    // We know pre_a@[j] is minimum of pre_a@[j..f). So pre_a@[j] <= pre_a@[k].
                                    // And a@[k] is pre_a@[k]. So new_j_minus_1_val <= a@[k].
                                    assert(pre_a@[j] <= pre_a@[k]); // From pre_a j-loop invariant
                                    assert(new_j_minus_1_val == pre_a@[j]);
                                    assert(a@[k] == pre_a@[k]);
                                    assert(new_j_minus_1_val <= a@[k]);
                                }
                            }
                        }
                    }
                    j = j - 1;
                }
                proof {
                    // After the inner loop completes (j == i), the inner loop invariant states:
                    // forall|k: int| (i < k && k < f && k >= i) ==> a@[i] <= a@[k].
                    // This simplifies to forall|k: int| (i < k && k < f) ==> a@[i] <= a@[k].
                    // This means a[i] is the minimum element in a[i..f).
                    // We need to show sorted_seg(a@, c as int, (i+1) as int).
                    // We already have sorted_seg(a@, c as int, i as int) by outer loop invariant.
                    // This means forall l,k: c <= l <= k < i ==> a@[l] <= a@[k].
                    // To extend this to i+1, we need to prove that:
                    // 1. a@[i] is sorted relative to a@[i+1 .. f) which we just proved.
                    // 2. a@[i-1] <= a@[i] (if i > c).
                    // We know a@[i] is the minimum of a@[i..f).
                    // We know from sorted_seg(a@, c, i) that a@[c] <= ... <= a@[i-1].
                    // The property that a@[i-1] <= a@[i] is crucial.
                    // This property comes directly from having moved the smallest element of a[i..f) to a[i],
                    // and knowing that all elements in a[c..i) are <= this minimum.
                    // This must be true in the post-state.
                    // Consider previous outer loop iteration's `i_prev = i-1`.
                    // At `i_prev`, `a[i-1]` was set to `min(old_a[i-1 .. f))`.
                    // And `a[i]` was some value.
                    // Now, `a[i]` gets `min(old_a[i..f))`.
                    // It is required that `a[i-1] <= a[i]`.
                    // This can be proven as follows:
                    // By `sorted_seg(a@, c as int, i as int)`, we have `a@[i-1]` is the largest element in the `a@[c..i)`.
                    // Also, we know `a@[i-1]` was `min(old(a)[i-1..f))`.
                    // And `a@[i]` now is `min(old(a)[i..f))`.
                    // Since `old(a)[i-1]` is included in the set `old(a)[i-1..f)`, its minimum is `<= old(a)[i-1]`.
                    // And `old(a)[i]` is included in `old(a)[i..f)`, its minimum is `<= old(a)[i]`.
                    // Furthermore, `old(a)[i]` must be one of the elements for which `old(a)[i-1]` was selected as minimum.
                    // This means `old(a)[i-1] <= old(a)[i]`.
                    // So `a@[i-1]` (which is `old_a[i-1]`) <= `a@[i]` (which is `min(old_a[i..f))`).
                    // This is the property that needs to hold.
                    // This is exactly the selection sort invariant.
                    assert forall|l: int, k: int| (c <= l && l <= k && k < (i+1) as int) implies a@[l] <= a@[k] by {
                        if k < i { // l, k are both within the already sorted prefix
                            assert(l < i);
                            assert(a@[l] <= a@[k]); // From sorted_seg(a@, c, i)
                        } else if k == i { // l < i and k == i
                            assert(l < i);
                            // We know a[i] is the min of a[i..f).
                            // We need to show a[l] <= a[i] for l < i.
                            // The outer loop invariant guarantees that a[l] <= a[i_prev] for l < i_prev.
                            // The `sorted_seg(a@, c as int, i as int)` means `a[l] <= a[i-1]` for `l < i-1`.
                            // So we need to show `a[i-1] <= a[i]`.
                            // `a[i-1]` is the element that was put there in the previous iteration of the outer loop.
                            // At that point, `a[i-1]` was the minimum of `a[i-1..f)`.
                            // Now `a[i]` is the minimum of `a[i..f)`.
                            // Since `a[i]` is an element in `a[i-1..f)`, and `a[i-1]` is the minimum of `a[i-1..f)`,
                            // it must be that `a[i-1] <= a[i]`.
                            let val_at_i_minus_1 = a@[(i-1) as int];
                            assert(sorted_seg(a@, c as int, i as int));
                            assert forall|m: int| (i < m && m < f) implies a@[i] <= a@[m]; // From j loop post
                            if i > c {
                                // `a@[i-1]` is what was put there previously, which means it was the minimum of `old(a)[i-1..f)`.
                                // `a@[i]` is the minimum of `current_a[i..f)`.
                                // Since `a@[i]` is one of the elements that `a@[i-1]` was compared against when it was selected,
                                // we must have `a@[i-1] <= a@[i]`.
                                #[verus::proof] {
                                    let s_orig = old(a)@; // The array before current outer loop iter (before j loop started)
                                    // At the entry of the outer loop, a@ corresponds to what it was after the (i-1)th iteration.
                                    // So `s_orig[i-1]` is the minimum of `original_segment_at_i_minus_1[i-1 .. f)`.
                                    // And now, `a@[i]` is the minimum of `s_orig[i .. f)`.
                                    // Since `s_orig[i]` is part of `s_orig[i-1 .. f)`, and `s_orig[i-1]` is the min of that broader segment,
                                    // it implies `s_orig[i-1] <= s_orig[i]`.
                                    // The inner loop only swaps elements within `a[i..f)`. The elements `a[0..i)` are left untouched.
                                    // So, `a@[i-1]` is the same as `old(a)@[i-1]`.
                                    // And `a@[i]` is `min_val(old(a)@[i..f), f, i)`.
                                    // The current value of `a@[i-1]` was established in the previous iteration of the outer loop.
                                    // At that time, `a@[i-1]` was made the minimum of `a@[i-1 .. f)`.
                                    // The current `a@[i]` is the minimum of the range `a@[i .. f)`.
                                    // Since `a@[i]` belongs to the range `a@[i-1 .. f)`, and `a@[i-1]` is the minimum of `a@[i-1 .. f)`,
                                    // it must logically follow that `a@[i-1] <= a@[i]`.
                                    // Need a helper function for `min_val`
                                    // Or just prove it explicitly
                                    // This requires a property for sorted segment that `a[x] <= a[y]` for x < y (implies it from current proof context)
                                    // Using `sorted_seg(a@, c as int, i as int)` we have `a[l] <= a[i-1]` for `l < i-1`.
                                    // From the inner loop post-condition, we have `a[i] <= a[k]` for `i < k < f`.
                                    // We need `a[i-1] <= a[i]`.
                                    // Let `s_at_i_minus_1` be the sequence `a@` when `i` was `i-1`.
                                    // `s_at_i_minus_1[i-1]` was `min(s_at_i_minus_1[i-1..f))`.
                                    // The current `a@` in this proof context is `s_at_i_minus_1` with `a[i]` updated.
                                    // The elements `a[c..i)` are stable (not changed by current iteration's inner loop).
                                    // So `a[i-1]` is the value set in the previous iteration.
                                    // That means that `a[i-1]` is indeed `min_of_original_segment_from_i_minus_1_to_f`.
                                    // And the current `a[i]` is `min_of_original_segment_from_i_to_f`.
                                    // Any elements in `a[i .. f)` are also in `a[i-1 .. f)`.
                                    // Thus `min(a[i-1 .. f)) <= min(a[i .. f))`, which implies `a[i-1] <= a[i]`.
                                }
                                assert(a@[l] <= a@[i]);
                            }
                        }
                    }
                }
            i = i + 1;
        }
    }
}
// </vc-code>

fn main() {}

}