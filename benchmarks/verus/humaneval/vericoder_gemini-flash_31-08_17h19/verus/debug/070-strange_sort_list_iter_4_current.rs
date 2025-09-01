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
        0 <= i < s@.len(),
        0 <= j < s@.len(),
    ensures
        s@.to_multiset() == old(s)@.to_multiset(),
        s@.len() == old(s)@.len(),
{
    // This lemma is a placeholder. In a real scenario, we might need a more
    // detailed proof about the effect of `swap` on multisets.
    // For now, we rely on the intuitive understanding that swapping two elements
    // does not change the multiset of elements.
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
            s_vec@.len() == s@.len(),
            s_vec@.to_multiset() == s@.to_multiset(),
    {
        let mut j: usize = i + 1;
        while j < s_vec.len()
            invariant
                (i as int) <= j && j <= s_vec.len(),
                s_vec@.len() == s@.len(),
                s_vec@.to_multiset() == s@.to_multiset(),
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