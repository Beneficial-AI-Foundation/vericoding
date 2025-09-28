use vstd::prelude::*;

verus! {

fn find_min_index(a: &Vec<i32>, s: usize, e: usize) -> (min_i: usize)
    requires 
        a.len() > 0,
        s < a.len(),
        e <= a.len(),
        e > s,
    ensures 
        min_i >= s,
        min_i < e,
        forall|k: int| s <= k < e ==> a[min_i as int] <= a[k],
{
    assume(false);
    s
}

spec fn is_sorted(ss: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < ss.len() ==> ss[i] <= ss[j]
}

spec fn is_permutation(a: Seq<i32>, b: Seq<i32>) -> bool
    decreases a.len(), b.len()
{
    a.len() == b.len() && 
    ((a.len() == 0 && b.len() == 0) ||  
     (exists|i: int, j: int| {
        0 <= i < a.len() && 0 <= j < b.len() && a[i] == b[j] && 
        is_permutation(
            a.subrange(0, i) + {if i < a.len() { a.subrange(i + 1, a.len() as int) } else { seq![] }},
            b.subrange(0, j) + {if j < b.len() { b.subrange(j + 1, b.len() as int) } else { seq![] }}
        )
     }))
}

spec fn is_permutation2(a: Seq<i32>, b: Seq<i32>) -> bool {
    a.to_multiset() == b.to_multiset()
}

// <vc-helpers>
fn find_min_index(a: &Vec<i32>, s: usize, e: usize) -> (min_i: usize)
    requires
        a.len() > 0,
        s < a.len(),
        e <= a.len(),
        e > s,
    ensures
        min_i >= s,
        min_i < e,
        forall|k: int| s <= k < e ==> a[min_i as int] <= a[k],
{
    let mut min_idx = s;
    let mut i = s + 1;

    #[verus::invariant(
        i <= e,
        min_idx >= s,
        min_idx < i,
        forall|k: int| (s <= k && k < i) ==> a[min_idx as int] <= a[k],
    )]
    while i < e {
        if a[i] < a[min_idx] {
            min_idx = i;
        }
        i += 1;
    }
    min_idx
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(ns: &mut Vec<i32>) 
    requires old(ns).len() >= 0
    ensures 
        is_sorted(ns@),
        is_permutation2(old(ns)@, ns@),
// </vc-spec>
// <vc-code>
{
    let original_seq = ns@;
    let len = ns.len();

    #[verus::invariant(
        len == ns.len(),
        i <= len,
        is_sorted(ns@.subrange(0, i as int)),
        is_permutation2(original_seq, ns@),
        forall|k: int| i <= k < len ==> (
            forall|other_k: int| 0 <= other_k < i ==> ns@[other_k] <= ns@[k]
        ),
    )]
    for i in 0..len {
        let min_idx = find_min_index(ns, i, len);

        // Prove that min_idx is the smallest overall from i to len-1
        proof {
            assert(min_idx >= i);
            assert(min_idx < len);
            assert(forall|k: int| i <= k < len ==> ns@[min_idx as int] <= ns@[k]);
        }

        // Swap ns[i] and ns[min_idx]
        let temp = ns[i];
        let val_at_min_idx = ns[min_idx];
        let pre_swap = ns@;

        ns.set(i, val_at_min_idx);
        ns.set(min_idx, temp);

        // Prove properties of the swapped array for the invariant
        proof {
            assert(is_permutation2(pre_swap, ns@)); // The swap preserves the multiset
            assert(is_permutation2(original_seq, ns@)); // The swap preserves the multiset

            assert(is_sorted(ns@.subrange(0, (i + 1) as int))) by {
                // The new element at index i (val_at_min_idx) is the minimum in the range [i, len)
                // We need to show that it is greater than or equal to all elements in [0, i)
                assert forall |k_inner: int| 0 <= k_inner < i implies ns@[k_inner] <= ns@[i] by {
                    assert(k_inner < i);
                    assert(ns@[k_inner] == pre_swap@[k_inner as int]); // Element at k_inner is unaffected by swap

                    assert(pre_swap@[k_inner as int] <= pre_swap@[min_idx as int]) by {
                        assert forall|k_orig: int| i <= k_orig < len ==> (forall|other_k_orig: int| 0 <= other_k_orig < i ==> pre_swap@[other_k_orig] <= pre_swap@[k_orig]) implies
                            pre_swap@[k_inner] <= pre_swap@[min_idx]
                        from (forall|k_orig: int| i <= k_orig < len ==> (forall|other_k_orig: int| 0 <= other_k_orig < i ==> pre_swap@[other_k_orig] <= pre_swap@[k_orig]));
                    };
                    assert(ns@[i] == val_at_min_idx && val_at_min_idx == pre_swap@[min_idx as int]);
                    assert(ns@[k_inner] <= ns@[i]);
                }
                assert forall |k_inner: int| i <= k_inner < (i + 1) implies ns@[k_inner] <= ns@[i] by {
                    assert(k_inner == i); // only possible value for k_inner
                    assert(ns@[k_inner] == ns@[i]);
                }
            };

            assert forall|k: int| (i + 1) <= k < len implies (
                forall|other_k: int| 0 <= other_k < (i + 1) implies ns@[other_k] <= ns@[k]
            ) by {
                assert(k >= i + 1);
                assert(k < len);
                assert forall |other_k: int| 0 <= other_k < (i + 1) implies ns@[other_k] <= ns@[k] by {
                    if other_k < i {
                        // Current other_k is in the sorted prefix [0, i-1]
                        assert(ns@[other_k] == pre_swap@[other_k as int]); // Other_k is unaffected
                        assert(pre_swap@[other_k as int] <= pre_swap@[k as int]) by {
                            assert forall|k_orig: int| i <= k_orig < len ==> (forall|other_k_orig: int| 0 <= other_k_orig < i ==> pre_swap@[other_k_orig] <= pre_swap@[k_orig]) implies
                                pre_swap@[other_k] <= pre_swap@[k]
                            from (forall|k_orig: int| i <= k_orig < len ==> (forall|other_k_orig: int| 0 <= other_k_orig < i ==> pre_swap@[other_k_orig] <= pre_swap@[k_orig]));
                        };
                        assert(ns@[other_k] <= ns@[k]);

                    } else if other_k == i {
                        // Current other_k is the newly sorted element at index i
                        assert(ns@[i] == val_at_min_idx);
                        assert(val_at_min_idx == pre_swap@[min_idx as int]);
                        assert(pre_swap@[min_idx as int] <= pre_swap@[k as int]); // From find_min_index postcondition before swap
                        assert(ns@[i] <= ns@[k]);

                    } else {
                        // other_k cannot be > i as it is strictly less than i+1
                        assert(false);
                    }
                }
            }
        }
    }
}
// </vc-code>

fn main() {}

}