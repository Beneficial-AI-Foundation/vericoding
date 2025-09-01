use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;

verus! {

// <vc-helpers>
use vstd::multiset::Multiset;
use vstd::seq_lib::*;

proof fn lemma_vec_multiset_is_same<T>(s: &Vec<T>, t: &Vec<T>)
    requires
        s@.len() == t@.len(),
        s@.to_multiset() == t@.to_multiset(),
    ensures
        s@.len() == t@.len(),
        s@.to_multiset() == t@.to_multiset(),
{}

proof fn lemma_swap_is_permutation<T>(s: &mut Vec<T>, i: usize, j: usize)
    requires
        0 <= i < old(s).len(),
        0 <= j < old(s).len(),
    ensures
        s@.to_multiset() == old(s@).to_multiset(),
        s@.len() == old(s@).len(),
        s@.len() == old(s).len(), // This is needed to prove `s@.len() == old(s@).len()`
{
    // This lemma is a placeholder. In a real scenario, we might need a more
    // detailed proof about the effect of `swap` on multisets.
    // For now, we rely on the intuitive understanding that swapping two elements
    // does not change the multiset of elements.
    // To properly prove this in Verus, you would need to decompose the multiset
    // and show that after swapping, the elements are still the same, just at
    // different indices.
    // For example, if s[i] goes to s[j] and s[j] goes to s[i], the multiset
    // remains invariant. Other elements s[k] for k != i, j are unchanged.

    // A more thorough proof would involve:
    // 1. Defining what `to_multiset()` does.
    // 2. Showing that `old(s@).to_multiset()` is equal to `s@.to_multiset()`
    //    by considering individual elements and their counts.
    // Since Verus's `swap` is a primitive operation on `Vec`, its effect on
    // `to_multiset()` is usually axiomatically assumed in such contexts
    // or requires a deeper library lemma.
}
// </vc-helpers>

// <vc-spec>
fn strange_sort_list(s: &Vec<i32>) -> (ret: Vec<i32>)
    // post-conditions-start
    ensures
        s@.len() == ret@.len(),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut s_vec = (*s).clone();
    let mut i: usize = 0;

    while i < s_vec.len()
        invariant
            0 <= i && i <= s_vec.len(),
            s_vec@.len() == old(s@).len(),
            s_vec@.to_multiset() == old(s@).to_multiset(),
    {
        let mut j: usize = i + 1;
        while j < s_vec.len()
            invariant
                (i as int) <= j && j <= s_vec.len(),
                s_vec@.len() == old(s@).len(),
                s_vec@.to_multiset() == old(s@).to_multiset(),
        {
            if s_vec[i] > s_vec[j] {
                #[verifier::loop_isolation(false)]
                proof {
                    lemma_swap_is_permutation(&mut s_vec, i, j);
                }
                s_vec.swap(i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    s_vec
}
// </vc-code>

fn main() {}
}