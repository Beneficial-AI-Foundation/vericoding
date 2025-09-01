use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;

verus! {

// <vc-helpers>
use vstd::multiset::Multiset;

proof fn lemma_vec_multiset_is_same<T>(s: &Vec<T>, t: &Vec<T>)
    requires
        s@.len() == t@.len(),
        s@.to_multiset() == t@.to_multiset(),
    ensures
        s@.len() == t@.len(),
        s@.to_multiset() == t@.to_multiset(),
{}
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
    let mut s_mut = s.clone();
    let mut i = 0;

    while i < s_mut.len()
        invariant
            0 <= i && i <= s_mut.len(),
    {
        let mut j = i + 1;
        while j < s_mut.len()
            invariant
                (i + 1) <= j && j <= s_mut.len(),
                s_mut@.len() == s@.len(),
                s_mut@.to_multiset() == s@.to_multiset(),
        {
            if s_mut.view_native()[i] > s_mut.view_native()[j] {
                s_mut.swap(i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    s_mut
}
// </vc-code>

fn main() {}
}